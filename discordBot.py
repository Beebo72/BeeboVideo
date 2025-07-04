# Everytime I come back to this project I realize how bad at programming I used to be

# TODO:
#   Every 5 minutes scan, with another bot, update the donor guilds/users.
#   Check owner of guild when processing command, apply relevent donor perks
#   Datamosh is broken
#   Thing likes to just not working a wholllllllle lot
#   Actually the entire codebase sucks
#   Rewrite the thing again to not suck and actually be readable and documented so other people can actually contribute

import os, sys, time, random, discord, requests, asyncio, logging, threading
from hashlib import sha256
from pyjson5 import load as json_load
from combiner import combiner
from editor.download import download
from collections import namedtuple, defaultdict
from func_helper import  *
from functools import reduce
from operator import add
from editor import editor
from math import ceil
from PIL import Image, ImageDraw, ImageFont
from io import BytesIO
from datetime import datetime
from discord import app_commands
import math

logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)
logger_handler = logging.StreamHandler(sys.stdout)
logger_handler.setLevel(logging.DEBUG)
logger.addHandler(logger_handler)
info = lambda *args: logger.info(' | '.join(map(str, args)))

config = json_load(open("config.json", 'r'))

FILE_SIZE_LIMIT_MB = 10 # My internet pls

message_search_count      = config["message_search_count"]
command_chain_limit       = config["command_chain_limit"]
working_directory         = os.path.realpath(config["working_directory"])
response_messages         = config["response_messages"]
max_concat_count          = config["max_concat_count"]
discord_token             = config["discord_token"]
meta_prefixes             = config["meta_prefixes"]
cookie_file               = config.setdefault("cookie_file")

disable_donor_check       = config.setdefault("disable_donor_check")
disable_guild_owner_check = config.setdefault("disable_guild_owner_check")
donor_guild_id            = config.setdefault("donor_guild_id")
donor_teir_roles          = config.setdefault("donor_teir_roles")
donor_guild_check_seconds = config.setdefault("donor_guild_check_seconds")
disable_guild_owner_author_check = config.setdefault("disable_guild_owner_author_check") # bruh

valid_video_extensions = ("mp4", "webm", "avi", "mkv", "mov")
valid_image_extensions = ("png", "gif", "jpg", "jpeg")
valid_extensions = valid_video_extensions + valid_image_extensions

hash_str = lambda s: str(sha256(s.encode()).digest().hex())[:32]
hash_filename = lambda s: f"{hash_str((q:=os.path.splitext(s))[0])}{q[1]}"

get_default = lambda v, d = config["unspecified_default_timeout"]: v["default"] if "default" in v else d
def config_timeout(default, custom):
    default_timeout = get_default(default)
    return defaultdict(
        lambda: defaultdict(
            lambda: default_timeout, **default
        ), **{
            k: defaultdict(
                lambda: get_default(v, default_timeout), **v
            ) for k, v in custom.items()})

guild_timeout_durations = config_timeout(config["default_guild_timeouts"], config["custom_guild_timeouts"])
user_timeout_durations = config_timeout(config["default_user_timeouts"], config["custom_user_timeouts"])
guild_timeouts = defaultdict(lambda: 0)
user_timeouts  = defaultdict(lambda: 0)

qued_msg = namedtuple("qued_msg", "context message filepath filename reply edit", defaults = 6 * [None])
result = namedtuple("result", "success filename message", defaults = 3 * [None])

async_runner = Async_handler()
taskList, messageQue = [], []

intents = discord.Intents.all()
intents.typing = False
intents.presences = False
# intents.members = False
discord_status = discord.Activity(type = discord.ActivityType.playing, name="Subscribe to @BTLE64 on YouTube")
bot = discord.AutoShardedClient(status=discord_status, intents=intents, chunk_guilds_at_startup=False)

COMMAND_COUNT_FILE = "CommandCount.dat"
COMMAND_LOG_FILE = "CommandHistory.dat"

# Load or initialize command count
if os.path.exists(COMMAND_COUNT_FILE):
    with open(COMMAND_COUNT_FILE, "r") as f:
        try:
            command_count = int(f.read().strip())
        except ValueError:
            command_count = 0
else:
    command_count = 0

# Start time
start_time = time.time()

def get_uptime():
    """Calculate bot uptime."""
    seconds = int(time.time() - start_time)
    hours, remainder = divmod(seconds, 3600)
    minutes, seconds = divmod(remainder, 60)
    return f"{hours}h {minutes}m {seconds}s"

class target_group:
    def __init__(self, attachments, reply, channel):
        self.attachments = attachments
        self.reply       = reply
        self.channel     = channel
    def compile(self):
        k = []; [k.append(i) for i in (self.attachments + self.reply + self.channel) if i not in k]
        return k

def human_size(size, units="B|KB|MB|GB|TB|PB|EB".split('|')): # https://stackoverflow.com/a/43750422/14501641
    return str(size) + units[0] if size < 1024 else human_size(size >> 10, units[1:])

def generate_uuid_from_msg(msg_id):
    return f"{msg_id}_{(time.time_ns() // 100) % 1000000}"

def generate_uuid_folder_from_msg(msg_id):
    return f"{working_directory}/{generate_uuid_from_msg(msg_id)}"

def clean_message(msg):
    return msg.replace(chr(8206), '').replace('@', '@'+chr(8206))

def apply_timeouts(msg, command,
        guild_timeout_durations=guild_timeout_durations,
        user_timeout_durations=user_timeout_durations,
        guild_timeouts=guild_timeouts,
        user_timeouts=user_timeouts):
        
    ahr_id = str(msg.author.id)
    
    if disable_guild_owner_check:
        gld_id = '0'
    else:
        try:
            gld_id = str(msg.guild.id)
        except AttributeError:
            gld_id = '0'
            print(f"Error aquiring guild ID for author ID {ahr_id}")
    
    if disable_guild_owner_author_check:
        gld_own_id = '0'
    else:
        try:
            if gld_id == '0':
                gld_own_id = '0'
            else:
                gld_own_id = str(msg.guild.owner.id)
        except AttributeError:
            gld_own_id = '0'
            print(f"Error aquiring owner ID for guild ID {gld_id}")
    
    if "ghost" in user_timeout_durations[ahr_id] or "ghost" in guild_timeout_durations[gld_id]:
        return True
    
    gt, ut = guild_timeouts[gld_id], user_timeouts[ahr_id]
    is_donor_user = "donor" in user_timeout_durations[ahr_id]
    is_donor_guild = "donor" in user_timeout_durations[gld_own_id]
    
    ct = time.time()
    if not is_donor_user and ct < gt:
        return gt - ct
    if ct < ut:
        return ut - ct
    
    user_timeouts[ahr_id] = ct + user_timeout_durations[ahr_id][command] * (
        user_timeout_durations[ahr_id]["user_timeout_multiplier"] if is_donor_user else 1)
    if not is_donor_user:
        guild_timeouts[gld_id] = ct + guild_timeout_durations[gld_id][command] * (
            user_timeout_durations[gld_own_id]["guild_timeout_multiplier"] if is_donor_guild else 1)
    
    return True

def apply_timeouts2(msg, command,
        guild_timeout_durations=guild_timeout_durations,
        user_timeout_durations=user_timeout_durations,
        guild_timeouts=guild_timeouts,
        user_timeouts=user_timeouts):
        
    ahr_id = str(msg.user.id)
    gld_id = '0'
    gld_own_id = '0'
    
    if "ghost" in user_timeout_durations[ahr_id] or "ghost" in guild_timeout_durations[gld_id]:
        return True
    
    gt, ut = guild_timeouts[gld_id], user_timeouts[ahr_id]
    is_donor_user = "donor" in user_timeout_durations[ahr_id]
    is_donor_guild = "donor" in user_timeout_durations[gld_own_id]
    
    ct = time.time()
    if not is_donor_user and ct < gt:
        return gt - ct
    if ct < ut:
        return ut - ct
    
    user_timeouts[ahr_id] = ct + user_timeout_durations[ahr_id][command] * (
        user_timeout_durations[ahr_id]["user_timeout_multiplier"] if is_donor_user else 1)
    if not is_donor_user:
        guild_timeouts[gld_id] = ct + guild_timeout_durations[gld_id][command] * (
            user_timeout_durations[gld_own_id]["guild_timeout_multiplier"] if is_donor_guild else 1)
    
    return True



async def check_donors():
    global guild_timeout_durations, user_timeout_durations
    
    count = 0
    while True:
        await tree.sync()
        info("🔁 Syncing command tree")
        await asyncio.sleep(donor_guild_check_seconds)
        count += 1

async def processQue():
    while True:
        if not len(messageQue):
            await asyncio.sleep(1)
            continue
        
        res = messageQue.pop(0)
        
        try:
            action = res.context.reply if res.reply else (res.context.edit if res.edit else res.context.channel.send)
            if res.filepath:
                if (filesize := os.path.getsize(res.filepath)) >= FILE_SIZE_LIMIT_MB * 1024 ** 2:
                    await action(f":x: Sorry, but the resulting file ({human_size(filesize)}) is over the {FILE_SIZE_LIMIT_MB}MB file size limit.")
                else:
                    with open(res.filepath, 'rb') as f:
                        args = [res.message] if res.message else []
                        file_kwargs = {"filename": res.filename} if res.filename else {}
                        if res.message and res.context.content.startswith('!') and (action == res.context.reply and res.context.author.id == bot.user.id):
                            await res.context.delete()
                            await asyncio.sleep(1)
                            await res.context.channel.send(*args, file = discord.File(f, **file_kwargs))
                        else:
                            await action(*args, file = discord.File(f, **file_kwargs))
            else:
                await action(res.message)
        except Exception as err:
            print(f'Unable to post a message, "{err}"')
            await asyncio.sleep(0.5)

async def get_targets(msg, attachments = True, reply = True, channel = True, message_search_count = 8, stop_on_first = True):
    msg_attachments, msg_reply, msg_channel = [], [], []
    
    async def do_setters():
        nonlocal msg_attachments, msg_reply, msg_channel
        if attachments: msg_attachments = msg.attachments
        if stop_on_first and msg_attachments: return
        
        if reply and msg.reference: msg_reply = (await msg.channel.fetch_message(msg.reference.message_id)).attachments
        if stop_on_first and msg_reply: return
        
        if channel and message_search_count > 0: msg_channel = reduce(add, [i.attachments async for i in msg.channel.history(limit = message_search_count)])
    await do_setters()
    
    return target_group(msg_attachments, msg_reply, msg_channel)

async def get_targets_slash(msg, attachments = True, reply = True, channel = True, message_search_count = 8, stop_on_first = True):
    msg_attachments, msg_reply, msg_channel = [], [], []
    
    async def do_setters():
        nonlocal msg_attachments, msg_reply, msg_channel
        if attachments: msg_attachments = msg[0]
        if stop_on_first and msg_attachments: return
    await do_setters()
    
    return target_group(msg_attachments, msg_reply, msg_channel)

def download_discord_attachment(target, filename, keep_ext = False):
    if keep_ext:
        filename = f"{filename}.{os.path.splitext(target.filename)[1][1:]}"
    with open(filename, 'wb') as f:
        f.write(requests.get(target.url).content)
    return filename

def download_discord_attachments(targets, folder):
    if not os.path.isdir(folder):
        os.makedirs(folder)
    return [download_discord_attachment(t, folder + '/' + generate_uuid_from_msg(t.id), keep_ext = False) for t in targets]

async def prepare_VideoEdit(msg):
    targets = (await get_targets(msg, message_search_count = message_search_count)).compile()
    if not targets:
        await msg.channel.send("Unable to find a message to edit, maybe upload a video and try again?")
        return
    
    file_ext = os.path.splitext(targets[0].filename)[1][1:]
    if file_ext not in valid_extensions:
        await msg.channel.send(f":x: File type not valid, valid file types are: `{'`, `'.join(valid_extensions)}`")
        return
    
    return targets[0], f"{generate_uuid_folder_from_msg(msg.id)}.{file_ext}"

async def prepare_VideoEdit_SlashCmd(msg):
    targets = (await get_targets_slash(msg, message_search_count = message_search_count)).compile()
    if not targets:
        await msg.og.followup.send("Unable to find a message to edit, maybe upload a video and try again?")
        return
    
    file_ext = os.path.splitext(targets[0].filename)[1][1:]
    if file_ext not in valid_extensions:
        await msg.og.followup.send(f":x: File type not valid, valid file types are: `{'`, `'.join(valid_extensions)}`")
        return
    
    return targets[0], f"{generate_uuid_folder_from_msg(msg[1])}.{file_ext}"


async def prepare_concat(msg, args):
    concat_count, *name_spec = params if len(params := args.split()) else '2'
    try:
        concat_count = min(max_concat_count, max(2, (int(concat_count) if len(concat_count.strip()) else len(msg.attachments))))
    except Exception as err:
        await msg.reply(f':x: No video amount given, interpreting "{concat_count}" as specifier...')
        name_spec.insert(0, concat_count)
        concat_count = min(max_concat_count, max(2, len(name_spec)))
    
    targets_unsorted = list(filter(
        lambda t: os.path.splitext(t.filename)[1][1:] in valid_video_extensions,
        (await get_targets(msg, message_search_count = message_search_count, stop_on_first = False)).compile()
    ))[:concat_count]
    
    if len(targets_unsorted) < 2:
        await msg.reply(":x: Unable to find enough videos to combine.")
        return
    
    targets = []
    for s in map(lambda c: c.strip().lower(), name_spec):
        i = 0
        while i < len(targets_unsorted):
            if targets_unsorted[i].filename.lower().startswith(s):
                targets.append(targets_unsorted.pop(i))
            i += 1
    targets += targets_unsorted
    
    return targets

def get_next_milestone(command_count):
    """Find the next milestone (next multiple of 1000)."""
    return ((command_count // 1000) + 1) * 1000

def is_milestone(command_count):
    """Check if the count is a milestone (1000, 2000, etc.)."""
    return command_count % 1000 == 0 and command_count > 0

def process_result_post(msg, res, filename = "video.mp4", prefix = None, random_message = True):
    if res.success:
        text = random.choice(response_messages) if random_message else res.message
        global command_count
        command_count += 1
        print(f"The total amount has been increased to {command_count}")
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_entry = f"{timestamp} - edited video #{command_count})\n"
        # Save command count to file
        with open(COMMAND_COUNT_FILE, "w") as f:
            f.write(str(command_count))
        with open(COMMAND_LOG_FILE, "a") as log_file:
            log_file.write(log_entry)
        next_milestone = get_next_milestone(command_count)
        colefta = int(next_milestone) - int(command_count)
        if is_milestone(command_count):
            print("🎉🎉🎉🎉🎉🎉🎉🎉🎉🎉 WOWIE ZOWIE! NEW ACHIEVEMENT!! 🎉🎉🎉🎉🎉🎉🎉🎉🎉🎉")
            content = f"# YOU JUST EDITED THE {command_count}th VIDEO! :tada:\nPlease send proof to *beebo_robot64* **immediately** and join the bTLE64 server for the celebration!\n**See you there!**\n-# **#{command_count}**" if prefix else f"# YOU JUST EDITED THE {command_count}th VIDEO! :tada:\nPlease send proof to *beebo_robot64* **immediately** and join the BTLE64 server for the celebration!\n**See you there!**\n-# **#{command_count}**" 
        else:
            content = f"{text.strip()}\n{prefix.strip()}\n-# **#{command_count}**\n-# {colefta} left until {next_milestone}" if prefix else f"{text.strip()}\n-# **#{command_count}**\n-# {colefta} left until {next_milestone}" 
        messageQue.append(qued_msg(context = msg, filepath = res.filename, filename = hash_filename(filename), message = content, reply = True))
    else:
        messageQue.append(qued_msg(context = msg, message = res.message, reply = True))

async def process_result_post_SlashCmd(msg, res, filename = "video.mp4", prefix = None, random_message = True):
    if res.success:
        text = random.choice(response_messages) if random_message else res.message
        #messageQue.append(qued_msg(context = msg, filepath = res.filename, filename = hash_filename(filename), message = content, reply = True))
        if (filesize := os.path.getsize(res.filename)) >= FILE_SIZE_LIMIT_MB * 1024 ** 2:
            await msg.followup.send(f":x: Sorry, but the resulting file ({human_size(filesize)}) is over the {FILE_SIZE_LIMIT_MB}MB file size limit.")
        else:
            global command_count
            command_count += 1
            print(f"The total amount has been increased to {command_count}")
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            log_entry = f"{timestamp} - edited video #{command_count})\n"
            # Save command count to file
            with open(COMMAND_COUNT_FILE, "w") as f:
                f.write(str(command_count))
            with open(COMMAND_LOG_FILE, "a") as log_file:
                log_file.write(log_entry)
            next_milestone = get_next_milestone(command_count)
            colefta = int(next_milestone) - int(command_count)
            if is_milestone(command_count):
                print("🎉🎉🎉🎉🎉🎉🎉🎉🎉🎉 WOWIE ZOWIE! NEW ACHIEVEMENT!! 🎉🎉🎉🎉🎉🎉🎉🎉🎉🎉")
                content = f"# YOU JUST EDITED THE {command_count}th VIDEO! :tada:\nPlease send proof to *beebo_robot64* **immediately** and join the BTLE64 server for the celebration!\n**See you there!**\n-# **#{command_count}**" if prefix else f"# YOU JUST EDITED THE {command_count}th VIDEO! :tada:\nPlease send proof to *beebo_robot64* **immediately** and join the BTLE64 server for the celebration!\n**See you there!**\n-# **#{command_count}**" 
                await msg.followup.send(content, files=[discord.File(res.filename)], ephemeral=False)
            else:
                content = f"{text.strip()}\n`{prefix.strip()}`\n-# **#{command_count}**\n-# {colefta} left until {next_milestone}" if prefix else f"{text.strip()}\n-# **#{command_count}**\n-# {colefta} left until {next_milestone}" 
                await msg.followup.send(content, files=[discord.File(res.filename)], ephemeral=False)                
    else:
        #messageQue.append(qued_msg(context = msg, message = res.message, reply = True))
        await msg.followup.send(res.message)

async def parse_command(message):
    if (message.author.id == bot.user.id and not '║' in message.content) or (message.author.bot and message.author.id != bot.user.id):
        return

    original_msg = message.content
    msg = message.content.split('║', 1)[0]
    if len(msg) == 0: return
    
    try:
        is_reply_to_bot = message.reference and (await message.channel.fetch_message(message.reference.message_id)).author.id == bot.user.id
    except discord.errors.NotFound:
        is_reply_to_bot = False

    if message.author.id != bot.user.id and not is_reply_to_bot and msg.split('>>')[0].removeprefix('!').strip() == "":
        return
    
    has_meta_prefix = is_reply_to_bot
    append_space = ' ' if ' ' in msg else ''
    for pre in meta_prefixes:
        if msg.startswith(pre + append_space):
            has_meta_prefix = True
            msg = msg.removeprefix(pre).lstrip()
            break
    
    cmd_name_opts = ["concat", "combine", "download", "downloader", "bv"]
    
    author_id = str(message.author.id)
    
    chain_limit = 9999 if message.author.id == bot.user.id else (
        user_timeout_durations[author_id]["max_chain"] if (
            author_id in user_timeout_durations and "max_chain" in user_timeout_durations[author_id]
        ) else command_chain_limit)
    
    command, *remainder = msg.split(">>")[:chain_limit]
    if command.startswith('!'):
        command = command.removeprefix('!')
    
    remainder = clean_message('>>'.join(remainder)).strip()
    
    if len(remainder) and not any(remainder.removeprefix('!').startswith(i) for i in cmd_name_opts):
        remainder = f"bv {remainder}"
    
    spl = command.strip().split(' ', 1)
    cmd  = spl[0].strip()#.lower()
    args = spl[1].strip() if len(spl) > 1 else ""
    
    final_command_name = None
    if cmd in ["concat", "combine"]:
        final_command_name = "concat"
    elif cmd in ["download", "downloader"]:
        final_command_name = "download"
    elif cmd == "help":
        final_command_name = "help"
    elif cmd == "leaderboard.global":
        final_command_name = "leaderboard.global"
    elif cmd == "discord":
        final_command_name = "discord"
    elif cmd == "klaskysource":
        final_command_name = "klaskysource"
    elif cmd == "sysinfo":
        final_command_name = "sysinfo"
    elif (ev1 := (cmd in ["bv", ""])) or has_meta_prefix: # this part is janky
        final_command_name = "bv"
        if not ev1 or cmd == "":
            args = f"{spl[0].strip()} {args}" #

    if not final_command_name:
        return

    is_timeout = apply_timeouts(message, cmd, guild_timeout_durations, user_timeout_durations, guild_timeouts, user_timeouts)
    if is_timeout is not True:
        await message.reply(f"Please wait {ceil(is_timeout)} seconds to use this command again.")
        return

    match final_command_name:
        case "help":
            if 'ovb' in original_msg:
                await message.reply("VideoEditBot Command Documentation: https://github.com/GanerCodes/videoEditBot/blob/master/COMMANDS.md")
        case "discord":
            if 'ovb' in original_msg:
                await message.reply("Join our Discord server: https://discord.gg/yCVkJaDc37")
        case "sysinfo":
            if 'ovb' in original_msg:
                XXB = len(bot.guilds) / 100 * 100
                XXA = f"**{len(bot.guilds)}/100** {XXB:.1f}%"
                XYA = int(get_next_milestone(command_count))
                XYB = int(XYA) - int(command_count)
                embed = discord.Embed(title="OpenVideoBot System Info", color=discord.Color.purple())
                embed.add_field(name="Bot Uptime", value=get_uptime(), inline=False)
                embed.add_field(name="Total Files Edited", value=f"**{command_count}** edited so far - {XYB} until {XYA}", inline=False)
                embed.add_field(name="Servers", value=XXA, inline=False)
                await message.reply(embed=embed)     
        case "concat":
            Task(
                Action(prepare_concat, message, args,
                    name = "Concat Command Prep",
                    check = lambda x: x),
                Action(download_discord_attachments, swap_arg("result"), generate_uuid_folder_from_msg(message.id),
                    name = "Download videos to Concat",
                    check = lambda x: x),
                Action(combiner, swap_arg("result"), (concat_filename := f"{generate_uuid_folder_from_msg(message.id)}.mp4"),
                    SILENCE = "./editor/SILENCE.mp3",
                    print_info = False,
                    name = "Concat Videos",
                    fail_action = Action(
                        lambda n, e: messageQue.append(
                            qued_msg(
                                context = message,
                                message = "Sorry, something went wrong during concatenation.",
                                reply = True)))),
                Action(process_result_post, message, result(True, concat_filename, ""), concat_filename, remainder,
                    name = "Post Concat"),
                async_handler = async_runner
            ).run_threaded()
        case "download":
            Task(
                Action(download,
                    download_filename := f"{generate_uuid_folder_from_msg(message.id)}.mp4",
                    args, name="yt-dlp download", file_limit=FILE_SIZE_LIMIT_MB),
                Action(process_result_post, message, swap_arg("result"), download_filename,
                    remainder, name="Post Download"),).run_threaded()
        case "bv":
            print(f"{message.author} summoned OpenVideoBot")
            Task(
                Action(prepare_VideoEdit, message,
                    name = "VEB Command Prep",
                    check = lambda x: x,
                    parse = lambda x: {
                        "target": x[0],
                        "filename": x[1] },
                    skip_task_fail_handler = True),
                Action(download_discord_attachment, swap_arg("target"), swap_arg("filename"),
                    name = "VEB Download Target"),
                Action(editor, swap_arg("filename"), args, workingDir = working_directory, keepExtraFiles = False,
                    name = "VEB",
                    parse = lambda x: {
                        "result": x,
                        "filename": x.filename }),
                Action(process_result_post, message, swap_arg("result"), swap_arg("filename"), remainder,
                    name = "VEB Post"),
                async_handler = async_runner,
                persist_result_values = True
            ).run_threaded()
            
botReady = False
tree = app_commands.CommandTree(bot)
@bot.event
async def on_ready():
    global botReady, meta_prefixes
    if botReady: pass
    
    meta_prefixes += [
         f"<@{bot.user.id}>",
        f"<@!{bot.user.id}>",
        f"<@&{bot.user.id}>",
        f"<@#{bot.user.id}>"]
    
    if not os.path.isdir(working_directory):
        os.makedirs(working_directory)
    
    await bot.change_presence(status=discord.Status.dnd, activity = discord_status)
    if donor_guild_id and not disable_donor_check:
        asyncio.create_task(check_donors())
    asyncio.create_task(processQue())
    asyncio.create_task(async_runner.looper())
    
    botReady = True
    info("✅ OpenVideoBot is on")
    try:
        print("🔁 Syncing commands...")
        await tree.sync()
        print("✅ Sucessfully synced commands")
    except Exception as e:
        print(e)


@bot.event
async def on_message(msg):
    await parse_command(msg)

@tree.command(name="sysinfo", description="View the bot's system info.")
@app_commands.allowed_installs(guilds=True, users=True)
@app_commands.allowed_contexts(guilds=True, dms=True, private_channels=True)
async def sysinfo(message: discord.Interaction):
    XXB = len(bot.guilds) / 100 * 100
    XXA = f"**{len(bot.guilds)}/100** {XXB:.1f}%"
    XYA = int(get_next_milestone(command_count))
    XYB = int(XYA) - int(command_count)
    embed = discord.Embed(title="BeeboVideo System Info", color=discord.Color.blue())
    embed.add_field(name="Bot Uptime", value=get_uptime(), inline=False)
    embed.add_field(name="Total Files Edited", value=f"**{command_count}** edited so far - {XYB} until {XYA}", inline=False)
    embed.add_field(name="Servers", value=XXA, inline=False)
    await message.response.send_message(embed=embed)  

@tree.command(name="download", description="Tired of using BEB's text commands? Try this out!")
@app_commands.allowed_installs(guilds=True, users=True)
@app_commands.allowed_contexts(guilds=True, dms=True, private_channels=True)
async def download(message: discord.Interaction, args: str):
    await message.response.defer()
    print(f"Someone summoned OpenVideoBot")
    cmd_name_opts = ["concat", "combine", "download", "downloader", "destroy"]
    
    author_id = str(message.user.id)
    
    chain_limit = 9999 if message.user.id == bot.user.id else (
        user_timeout_durations[author_id]["max_chain"] if (
            author_id in user_timeout_durations and "max_chain" in user_timeout_durations[author_id]
        ) else command_chain_limit)
    
    command, *remainder = args.split(">>")[:chain_limit]
    if command.startswith('!'):
        command = command.removeprefix('!')
    
    remainder = clean_message('>>'.join(remainder)).strip()
    
    if len(remainder) and not any(remainder.removeprefix('!').startswith(i) for i in cmd_name_opts):
        remainder = f"destroy {remainder}"
    
    spl = command.strip().split(' ', 1)
    cmd  = spl[0].strip()#.lower()
    argz = spl[1].strip() if len(spl) > 1 else ""
    
    final_command_name = None
    if (ev1 := (cmd in ["download", "downloader", ""])) or True: # this part is janky
        final_command_name = "download"
        if not ev1 or cmd == "":
            argz = f"{spl[0].strip()} {argz}" #

    if not final_command_name:
        await message.followup.send("Please specify a file.")
        return

    is_timeout = apply_timeouts2(message, cmd, guild_timeout_durations, user_timeout_durations, guild_timeouts, user_timeouts)
    if is_timeout is not True:
        await message.followup.send(f"Please wait {ceil(is_timeout)} seconds to use this command again.")
        return
    
    match final_command_name:
        case "download":
            Task(
                Action(download,
                    download_filename := f"{generate_uuid_folder_from_msg(time.time_ns() // 100)}.mp4",
                    argz, name="yt-dlp download", file_limit=FILE_SIZE_LIMIT_MB,
                    parse = lambda x: {
                        "result": x,
                        "filename": x.filename }),
                Action(process_result_post_SlashCmd, message, swap_arg("result"), download_filename,
                    remainder, name="Post Download"),
                async_handler = async_runner,
                persist_result_values = True
                ).run_threaded()

@tree.command(name="beb", description="Tired of using BeeboVideos's text commands? Try this out!")
@app_commands.allowed_installs(guilds=True, users=True)
@app_commands.allowed_contexts(guilds=True, dms=True, private_channels=True)
async def ovb(message: discord.Interaction, args: str, file: discord.Attachment):
    await message.response.defer()
    print(f"Someone summoned BeeboVideo")
    cmd_name_opts = ["concat", "combine", "download", "downloader", "destroy"]
    
    author_id = str(message.user.id)
    
    chain_limit = 9999 if message.user.id == bot.user.id else (
        user_timeout_durations[author_id]["max_chain"] if (
            author_id in user_timeout_durations and "max_chain" in user_timeout_durations[author_id]
        ) else command_chain_limit)
    
    command, *remainder = args.split(">>")[:chain_limit]
    if command.startswith('!'):
        command = command.removeprefix('!')
    
    remainder = clean_message('>>'.join(remainder)).strip()
    
    if len(remainder) and not any(remainder.removeprefix('!').startswith(i) for i in cmd_name_opts):
        remainder = f"destroy {remainder}"
    
    spl = command.strip().split(' ', 1)
    cmd  = spl[0].strip()#.lower()
    argz = spl[1].strip() if len(spl) > 1 else ""
    
    final_command_name = None
    if cmd in ["concat", "combine"]:
        final_command_name = "concat"
    elif cmd in ["download", "downloader"]:
        final_command_name = "download"
    elif (ev1 := (cmd in ["destroy", ""])) or True: # this part is janky
        final_command_name = "destroy"
        if not ev1 or cmd == "":
            argz = f"{spl[0].strip()} {argz}" #

    if not final_command_name:
        await message.followup.send("Please specify a file.")
        return

    is_timeout = apply_timeouts2(message, cmd, guild_timeout_durations, user_timeout_durations, guild_timeouts, user_timeouts)
    if is_timeout is not True:
        await message.followup.send(f"Please wait {ceil(is_timeout)} seconds to use this command again.")
        return
    
    match final_command_name:
        case "destroy":
            Task(
                Action(prepare_VideoEdit_SlashCmd, [[file], (time.time_ns() // 100), message],
                    name = "VEB Command Prep",
                    check = lambda x: x,
                    parse = lambda x: {
                        "target": x[0],
                        "filename": x[1] },
                    skip_task_fail_handler = True),
                Action(download_discord_attachment, swap_arg("target"), swap_arg("filename"),
                    name = "VEB Download Target"),
                Action(editor, swap_arg("filename"), argz, workingDir = working_directory, keepExtraFiles = False,
                    name = "VEB",
                    parse = lambda x: {
                        "result": x,
                        "filename": x.filename }),
                Action(process_result_post_SlashCmd, message, swap_arg("result"), swap_arg("filename"), remainder,
                    name = "VEB Post"),
                async_handler = async_runner,
                persist_result_values = True
                ).run_threaded()
            

bot.run(discord_token)
