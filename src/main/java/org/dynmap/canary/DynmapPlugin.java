package org.dynmap.canary;

import java.io.File;
import java.net.InetSocketAddress;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.FutureTask;

import net.canarymod.Canary;
import net.canarymod.api.OfflinePlayer;
import net.canarymod.api.PlayerReference;
import net.canarymod.api.chat.ChatComponent;
import net.canarymod.api.entity.living.humanoid.CanaryPlayer;
import net.canarymod.api.entity.living.humanoid.Player;
import net.canarymod.api.world.Biome;
import net.canarymod.api.world.Chunk;
import net.canarymod.api.world.World;
import net.canarymod.api.world.blocks.Block;
import net.canarymod.api.world.blocks.BlockType;
import net.canarymod.api.world.blocks.Sign;
import net.canarymod.api.world.position.Location;
import net.canarymod.bansystem.Ban;
import net.canarymod.chat.MessageReceiver;
import net.canarymod.chat.ReceiverType;
import net.canarymod.commandsys.Command;
import net.canarymod.commandsys.CommandDependencyException;
import net.canarymod.commandsys.CommandListener;
import net.canarymod.config.Configuration;
import net.canarymod.exceptions.InvalidPluginException;
import net.canarymod.exceptions.PluginLoadFailedException;
import net.canarymod.hook.HookHandler;
import net.canarymod.hook.player.BedExitHook;
import net.canarymod.hook.player.BlockDestroyHook;
import net.canarymod.hook.player.BlockPlaceHook;
import net.canarymod.hook.player.ChatHook;
import net.canarymod.hook.player.ConnectionHook;
import net.canarymod.hook.player.DisconnectionHook;
import net.canarymod.hook.player.PlayerMoveHook;
import net.canarymod.hook.player.SignChangeHook;
import net.canarymod.hook.system.LoadWorldHook;
import net.canarymod.hook.system.PluginEnableHook;
import net.canarymod.hook.system.ServerTickHook;
import net.canarymod.hook.system.UnloadWorldHook;
import net.canarymod.hook.world.BlockGrowHook;
import net.canarymod.hook.world.BlockPhysicsHook;
import net.canarymod.hook.world.BlockUpdateHook;
import net.canarymod.hook.world.ChunkCreatedHook;
import net.canarymod.hook.world.DecorateHook;
import net.canarymod.hook.world.ExplosionHook;
import net.canarymod.hook.world.FlowHook;
import net.canarymod.hook.world.IgnitionHook;
import net.canarymod.hook.world.LeafDecayHook;
import net.canarymod.hook.world.LiquidDestroyHook;
import net.canarymod.hook.world.PistonExtendHook;
import net.canarymod.hook.world.PistonRetractHook;
import net.canarymod.hook.world.RedstoneChangeHook;
import net.canarymod.hook.world.IgnitionHook.IgnitionCause;
import net.canarymod.hook.world.TreeGrowHook;
import net.canarymod.logger.Logman;
import net.canarymod.plugin.Plugin;
import net.canarymod.plugin.PluginListener;
import net.canarymod.plugin.PluginManager;
import net.canarymod.plugin.Priority;
import net.canarymod.tasks.ServerTask;
import net.canarymod.tasks.ServerTaskManager;

import org.dynmap.DynmapChunk;
import org.dynmap.DynmapCommonAPI;
import org.dynmap.DynmapCommonAPIListener;
import org.dynmap.DynmapCore;
import org.dynmap.DynmapLocation;
import org.dynmap.DynmapWorld;
import org.dynmap.Log;
import org.dynmap.MapManager;
import org.dynmap.PlayerList;
import org.dynmap.common.BiomeMap;
import org.dynmap.common.DynmapCommandSender;
import org.dynmap.common.DynmapPlayer;
import org.dynmap.common.DynmapServerInterface;
import org.dynmap.common.DynmapListenerManager.EventType;
import org.dynmap.markers.MarkerAPI;
import org.dynmap.modsupport.ModSupportImpl;
import org.dynmap.utils.DynmapLogger;
import org.dynmap.utils.MapChunkCache;
import org.dynmap.utils.VisibilityLimit;

public class DynmapPlugin extends Plugin implements DynmapCommonAPI {
    private DynmapCore core;
    private CanaryServer server;
    private String version;
    public SnapshotCache sscache;
    public PlayerList playerList;
    private MapManager mapManager;
    public static DynmapPlugin plugin;
    public PluginManager pm;
    private BukkitEnableCoreCallback enabCoreCB = new BukkitEnableCoreCallback();
    private HashMap<String, CanaryModWorld> world_by_name = new HashMap<String, CanaryModWorld>();

    private long perTickLimit;
    
    private int chunks_in_cur_tick = 0;
    private long prev_tick;

    private HashMap<String, Integer> sortWeights = new HashMap<String, Integer>();
    /* Lookup cache */
    private World last_world;
    private CanaryModWorld last_bworld;
    
    private CanaryVersionHelper helper;
    
    private static class TaskRecord implements Comparable<Object>
    {
        private long ticktorun;
        private long id;
        private FutureTask<?> future;
        @Override
        public int compareTo(Object o)
        {
            TaskRecord tr = (TaskRecord)o;

            if (this.ticktorun < tr.ticktorun)
            {
                return -1;
            }
            else if (this.ticktorun > tr.ticktorun)
            {
                return 1;
            }
            else if (this.id < tr.id)
            {
                return -1;
            }
            else if (this.id > tr.id)
            {
                return 1;
            }
            else
            {
                return 0;
            }
        }
    }

    private final CanaryModWorld getWorldByName(String name) {
        if((last_world != null) && (last_world.getName().equals(name))) {
            return last_bworld;
        }
        return world_by_name.get(name);
    }
    private final CanaryModWorld getWorld(World w) {
        if(last_world == w) {
            return last_bworld;
        }
        CanaryModWorld bw = world_by_name.get(w.getName());
        if(bw == null) {
            bw = new CanaryModWorld(w);
            world_by_name.put(w.getName(), bw);
        }
        else if(bw.isLoaded() == false) {
            bw.setWorldLoaded(w);
        }
        last_world = w;
        last_bworld = bw;

        return bw;
    }
    final void removeWorld(World w) {
        world_by_name.remove(w.getName());
        if(w == last_world) {
            last_world = null;
            last_bworld = null;
        }
    }
    
    private class BukkitEnableCoreCallback extends DynmapCore.EnableCoreCallbacks {
        @Override
        public void configurationLoaded() {
            File st = new File(core.getDataFolder(), "renderdata/spout-texture.txt");
            if(st.exists()) {
                st.delete();
            }
        }
    }
    
    private static class BlockToCheck {
        Location loc;
        int typeid;
        byte data;
        String trigger;
    };
    private LinkedList<BlockToCheck> blocks_to_check = null;
    private LinkedList<BlockToCheck> blocks_to_check_accum = new LinkedList<BlockToCheck>();
    
    public DynmapPlugin() {
        plugin = this;
        helper = CanaryVersionHelper.getHelper();
        pm = Canary.pluginManager();
            
        ModSupportImpl.init();
    }
    
    /**
     * Server access abstraction class
     */
    public class CanaryServer extends DynmapServerInterface implements PluginListener {
        /* Server thread scheduler */
        private Object schedlock = new Object();
        private long cur_tick;
        private long next_id;
        private long cur_tick_starttime;
        private PriorityQueue<TaskRecord> runqueue = new PriorityQueue<TaskRecord>();

        @Override
        public int getBlockIDAt(String wname, int x, int y, int z) {
            World w = Canary.getServer().getWorld(wname);
            Chunk c = null;
            if (w != null) {
                c = w.getChunk(x >> 4, z >> 4);
            }
            if (c != null) {
                return c.getBlockTypeAt(x & 0xF,  y,  z & 0xF);
            }
            return -1;
        }

        @Override
        public void scheduleServerTask(Runnable run, long delay) {
            TaskRecord tr = new TaskRecord();
            tr.future = new FutureTask<Object>(run, null);

            /* Add task record to queue */
            synchronized (schedlock)
            {
                tr.id = next_id++;
                tr.ticktorun = cur_tick + delay;
                runqueue.add(tr);
            }
        }
        @Override
        public DynmapPlayer[] getOnlinePlayers() {
            List<Player> players = Canary.getServer().getPlayerList();
            DynmapPlayer[] dplay = new DynmapPlayer[players.size()];
            for(int i = 0; i < dplay.length; i++)
                dplay[i] = new BukkitPlayer(players.get(i));
            return dplay;
        }
        @Override
        public void reload() {
            PluginManager pluginManager = Canary.pluginManager();
            try {
                pluginManager.reloadPlugin("dynmap");
            } catch (PluginLoadFailedException e) {
            } catch (InvalidPluginException e) {
            }
        }
        @Override
        public DynmapPlayer getPlayer(String name) {
            Player p = Canary.getServer().getPlayer(name);
            if(p != null) {
                return new BukkitPlayer(p);
            }
            return null;
        }
        @Override
        public Set<String> getIPBans() {
            Ban[] blist = Canary.bans().getAllBans();
            Set<String> rslt = new HashSet<String>();
            for (Ban b : blist) {
                if (b.isIpBan()) {
                    rslt.add(b.getIp());
                }
            }
            return rslt;
        }
        @Override
        public <T> Future<T> callSyncMethod(Callable<T> task) {
            return callSyncMethod(task, 0);
        }
        public <T> Future<T> callSyncMethod(Callable<T> task, long delay)
        {
            TaskRecord tr = new TaskRecord();
            FutureTask<T> ft = new FutureTask<T>(task);
            tr.future = ft;

            /* Add task record to queue */
            synchronized (schedlock)
            {
                tr.id = next_id++;
                tr.ticktorun = cur_tick + delay;
                runqueue.add(tr);
            }

            return ft;
        }
        @Override
        public String getServerName() {
            return Configuration.getServerConfig().getMotd();
        }
        @Override
        public boolean isPlayerBanned(String pid) {
            return Canary.bans().isBanned(pid);
        }
        @Override
        public String stripChatColor(String s) {
            return org.dynmap.common.DynmapChatColor.stripColor(s);
        }
        private Set<EventType> registered = new HashSet<EventType>();
        @Override
        public boolean requestEventNotification(EventType type) {
            if(registered.contains(type))
                return true;
            switch(type) {
                case WORLD_LOAD:
                case WORLD_UNLOAD:
                    /* Already called for normal world activation/deactivation */
                    break;
                case WORLD_SPAWN_CHANGE:
                    //Canary.hooks().registerListener((new Listener() {
                    //    @EventHandler(priority=EventPriority.MONITOR, ignoreCancelled=true)
                    //    public void onSpawnChange(SpawnChangeEvent evt) {
                    //        CanaryModWorld w = getWorld(evt.getWorld());
                    //        core.listenerManager.processWorldEvent(EventType.WORLD_SPAWN_CHANGE, w);
                    //    }
                    //}, DynmapPlugin.this);
                    break;
                case PLAYER_JOIN:
                case PLAYER_QUIT:
                    /* Already handled */
                    break;
                case PLAYER_BED_LEAVE:
                    Canary.hooks().registerListener(new OurBedLeaveTrigger(), DynmapPlugin.this);
                    break;
                case PLAYER_CHAT:
                    Canary.hooks().registerListener(new OurPlayerChatTrigger(), DynmapPlugin.this);
                    break;
                case BLOCK_BREAK:
                    Canary.hooks().registerListener(new OurBreakTrigger(), DynmapPlugin.this);
                    break;
                case SIGN_CHANGE:
                    Canary.hooks().registerListener(new OurSignChangeTrigger(), DynmapPlugin.this);
                    break;
                default:
                    Log.severe("Unhandled event type: " + type);
                    return false;
            }
            registered.add(type);
            return true;
        }
        @Override
        public boolean sendWebChatEvent(String source, String name, String msg) {
            //DynmapWebChatEvent evt = new DynmapWebChatEvent(source, name, msg);
            //getServer().getPluginManager().callEvent(evt);
            //return ((evt.isCancelled() == false) && (evt.isProcessed() == false));
            return true;
        }
        @Override
        public void broadcastMessage(String msg) {
            Canary.getServer().broadcastMessage(msg);
        }
        @Override
        public String[] getBiomeIDs() {
            BiomeMap[] b = BiomeMap.values();
            String[] bname = new String[b.length];
            for(int i = 0; i < bname.length; i++)
                bname[i] = b[i].toString();
            return bname;
        }
        @Override
        public double getCacheHitRate() {
            return sscache.getHitRate();
        }
        @Override
        public void resetCacheStats() {
            sscache.resetStats();
        }
        @Override
        public DynmapWorld getWorldByName(String wname) {
            return DynmapPlugin.this.getWorldByName(wname);
        }
        @Override
        public DynmapPlayer getOfflinePlayer(String name) {
            OfflinePlayer op = Canary.getServer().getOfflinePlayer(name);
            if(op != null) {
                return new BukkitPlayer(op);
            }
            return null;
        }
        @Override
        public Set<String> checkPlayerPermissions(String player, Set<String> perms) {
            if (Canary.bans().isBanned(player)) {
                return Collections.emptySet();
            }
            OfflinePlayer p = Canary.getServer().getOfflinePlayer(player);
            if (p == null) {
                return Collections.emptySet();
            }
            Set<String> rslt = new HashSet<String>();
            for (String s : perms) {
                if (p.hasPermission(s)) {
                    rslt.add(s);
                }
            }
            return rslt;
        }
        @Override
        public boolean checkPlayerPermission(String player, String perm) {
            if (Canary.bans().isBanned(player)) {
                return false;
            }
            OfflinePlayer p = Canary.getServer().getOfflinePlayer(player);
            boolean rslt = false;
            if (p != null)
                rslt = p.hasPermission(perm);
            return rslt;
        }
        /**
         * Render processor helper - used by code running on render threads to request chunk snapshot cache from server/sync thread
         */
        @Override
        public MapChunkCache createMapChunkCache(DynmapWorld w, List<DynmapChunk> chunks, 
                boolean blockdata, boolean highesty, boolean biome, boolean rawbiome) {
            MapChunkCache c = w.getChunkCache(chunks);
            if(c == null) { /* Can fail if not currently loaded */
                return null;
            }
            if(w.visibility_limits != null) {
                for(VisibilityLimit limit: w.visibility_limits) {
                    c.setVisibleRange(limit);
                }
                c.setHiddenFillStyle(w.hiddenchunkstyle);
            }
            if(w.hidden_limits != null) {
                for(VisibilityLimit limit: w.hidden_limits) {
                    c.setHiddenRange(limit);
                }
                c.setHiddenFillStyle(w.hiddenchunkstyle);
            }
            if(c.setChunkDataTypes(blockdata, biome, highesty, rawbiome) == false) {
                Log.severe("CraftBukkit build does not support biome APIs");
            }
            if(chunks.size() == 0) {    /* No chunks to get? */
                c.loadChunks(0);
                return c;
            }

            final MapChunkCache cc = c;

            while(!cc.isDoneLoading()) {
                Future<Boolean> f = core.getServer().callSyncMethod(new Callable<Boolean>() {
                    public Boolean call() throws Exception {
                        boolean exhausted = true;
                        
                        if (prev_tick != cur_tick) {
                            prev_tick = cur_tick;
                            cur_tick_starttime = System.nanoTime();
                        }                            
                        if(chunks_in_cur_tick > 0) {
                            boolean done = false;
                            while (!done) {
                                int cnt = chunks_in_cur_tick;
                                if (cnt > 5) cnt = 5;
                                chunks_in_cur_tick -= cc.loadChunks(cnt);
                                exhausted = (chunks_in_cur_tick == 0) || ((System.nanoTime() - cur_tick_starttime) > perTickLimit);
                                done = exhausted || cc.isDoneLoading();
                            }
                        }
                        return exhausted;
                    }
                });
                if (f == null) {
                    return null;
                }
                Boolean delay;
                try {
                    delay = f.get();
                } catch (CancellationException cx) {
                    return null;
                } catch (ExecutionException ex) {
                    Log.severe("Exception while fetching chunks: ", ex.getCause());
                    return null;
                } catch (Exception ix) {
                    Log.severe(ix);
                    return null;
                }
                if((delay != null) && delay.booleanValue()) {
                    try { Thread.sleep(25); } catch (InterruptedException ix) {}
                }
            }
            /* If cancelled due to world unload return nothing */
            if(w.isLoaded() == false)
                return null;
            return c;
        }
        @Override
        public int getMaxPlayers() {
            return Canary.getServer().getMaxPlayers();
        }
        @Override
        public int getCurrentPlayers() {
            return Canary.getServer().getNumPlayersOnline();
        }
        @Override
        public boolean isModLoaded(String name) {
            return false;
        }
        @Override
        public String getModVersion(String name) {
            return null;
        }


        @Override
        public double getServerTPS() {
            return Canary.getServer().getTicksPerSecond();
        }
        
        @Override
        public String getServerIP() {
            return Configuration.getServerConfig().getBindIp();
        }

        @Override
        public Map<Integer, String> getBlockIDMap() {
            String[] bsn = helper.getBlockShortNames();
            HashMap<Integer, String> map = new HashMap<Integer, String>();
            for (int i = 0; i < bsn.length; i++) {
                if (bsn[i] != null) {
                    map.put(i, bsn[i]);
                }
            }
            return map;
        }
        
        @HookHandler
        public void tickEvent(ServerTickHook event)  {
            cur_tick_starttime = System.nanoTime();
            // Tick core
            if (core != null) {
                core.serverTick(Canary.getServer().getTicksPerSecond());
            }

            boolean done = false;
            TaskRecord tr = null;
            long now;

            synchronized(schedlock) {
                cur_tick++;
                now = System.nanoTime();
                tr = runqueue.peek();
                /* Nothing due to run */
                if((tr == null) || (tr.ticktorun > cur_tick) || ((now - cur_tick_starttime) > perTickLimit)) {
                    done = true;
                }
                else {
                    tr = runqueue.poll();
                }
            }
            while (!done) {
                tr.future.run();

                synchronized(schedlock) {
                    tr = runqueue.peek();
                    now = System.nanoTime();
                    /* Nothing due to run */
                    if((tr == null) || (tr.ticktorun > cur_tick) || ((now - cur_tick_starttime) > perTickLimit)) {
                        done = true;
                    }
                    else {
                        tr = runqueue.poll();
                    }
                }
            }
            if (mapManager != null) {
                chunks_in_cur_tick = mapManager.getMaxChunkLoadsPerTick();
            }
        }

    }
    /**
     * Player access abstraction class
     */
    public class BukkitPlayer extends CanaryCommandSender implements DynmapPlayer {
        private PlayerReference player;
        
        public BukkitPlayer(Player p) {
            super(p);
            player = p;
        }
        public BukkitPlayer(OfflinePlayer p) {
            super(null);
            player = p;
        }
        @Override
        public boolean isConnected() {
            return player.isOnline();
        }
        @Override
        public String getName() {
            return player.getName();
        }
        @Override
        public String getDisplayName() {
            if (player instanceof Player) {
                ChatComponent dname = ((Player)player).getDisplayNameComponent();
                if (dname != null) {
                    return dname.getText();
                }
            }
            return player.getName();
        }
        @Override
        public boolean isOnline() {
            return player.isOnline();
        }
        @Override
        public DynmapLocation getLocation() {
            if (player instanceof Player) {
                Location loc = ((Player)player).getLocation(); // Use eye location, since we show head 
                if (loc != null) {
                    return toLoc(loc);
                }
            }
            return null;
        }
        @Override
        public String getWorld() {
            if(player == null) {
                return null;
            }
            World w = player.getWorld();
            if(w != null)
                return DynmapPlugin.this.getWorld(w).getName();
            return null;
        }
        @Override
        public InetSocketAddress getAddress() {
            if (player instanceof Player) {
                return (InetSocketAddress) ((Player) player).getNetServerHandler().getSocketAdress();
            }
            return null;
        }
        @Override
        public boolean isSneaking() {
            if(player instanceof Player)
                return ((Player)player).isSneaking();
            return false;
        }
        @Override
        public double getHealth() {
            if(player != null)
                return player.getHealth();
            else
                return 0;
        }
        @Override
        public int getArmorPoints() {
            if (player instanceof CanaryPlayer) {
                return ((CanaryPlayer)player).getHandle().bq();
            }
            return 0;
        }
        @Override
        public DynmapLocation getBedSpawnLocation() {
            Location loc = player.getHome();
            if(loc != null) {
                return toLoc(loc);
            }
            return null;
        }
        @Override
        public long getLastLoginTime() {
            //return player.getLastJoined();
            return 0;
        }
        @Override
        public long getFirstLoginTime() {
            //return player.getFirstPlayed();
            return 0;
        }
        @Override
        public boolean isInvisible() {
            if(player != null) {
                return ((Player)player).isHiddenFromAll();
            }
            return false;
        }
        @Override
        public int getSortWeight() {
            Integer wt = sortWeights.get(getName());
            if (wt != null)
                return wt;
            return 0;
        }
        @Override
        public void setSortWeight(int wt) {
            if (wt == 0) {
                sortWeights.remove(getName());
            }
            else {
                sortWeights.put(getName(), wt);
            }
        }
    }
    /* Handler for generic console command sender */
    public class CanaryCommandSender implements DynmapCommandSender {
        private MessageReceiver sender;

        public CanaryCommandSender(MessageReceiver send) {
            sender = send;
        }
        
        @Override
        public boolean hasPrivilege(String privid) {
            if(sender != null)
                return sender.hasPermission(privid);
            return false;
        }

        @Override
        public void sendMessage(String msg) {
            if(sender != null)
                sender.message(msg);
        }

        @Override
        public boolean isConnected() {
            if(sender != null)
                return true;
            return false;
        }
        @Override
        public boolean isOp() {
            if(sender != null) {
                return (sender.getReceiverType() == ReceiverType.SERVER) || ((sender instanceof Player) && ((Player)sender).isOperator());
            }
            else
                return false;
        }
        @Override
        public boolean hasPermissionNode(String node) {
            if (sender != null) {
                return sender.hasPermission(node);
            }
            return false;
        }
    }
    
    public void loadExtraBiomes(String mcver) {
        int cnt = 0;
        
        BiomeMap.loadWellKnownByVersion(mcver);
        /* Find array of biomes in biomebase */
        Biome[] biomelist = helper.getBiomeBaseList();
        /* Loop through list, skipping well known biomes */
        for(int i = 0; i < biomelist.length; i++) {
            Biome bb = biomelist[i];
            if(bb != null) {
                float tmp = bb.getTemperature();
                float hum = (float) ((double)bb.getRainfall() / 65536.0);
                BiomeMap bmap = BiomeMap.byBiomeID(i);
                if (bmap.isDefault()) {
                    String id =  helper.getBiomeBaseIDString(bb);
                    if(id == null) {
                        id = "BIOME_" + i;
                    }
                    BiomeMap m = new BiomeMap(i, id, tmp, hum);
                    Log.verboseinfo("Add custom biome [" + m.toString() + "] (" + i + ")");
                    cnt++;
                }
                else {
                    bmap.setTemperature(tmp);
                    bmap.setRainfall(hum);
                }
            }
        }
        if(cnt > 0) {
            Log.info("Added " + cnt + " custom biome mappings");
        }
    }
    

    private static class OurLogger implements DynmapLogger {
        private Logman lm;

        public OurLogger(Logman lm) {
            this.lm = lm;
        }
        @Override
        public void info(String msg) {
            lm.info(msg);
        }

        @Override
        public void verboseinfo(String msg) {
            lm.info(msg);
        }

        @Override
        public void severe(Throwable e) {
            lm.error(e.getMessage(), e);
        }

        @Override
        public void severe(String msg) {
            lm.error(msg);
        }

        @Override
        public void severe(String msg, Throwable e) {
            lm.error(msg, e);
        }

        @Override
        public void warning(String msg) {
            lm.warn(msg);
        }

        @Override
        public void warning(String msg, Throwable e) {
            lm.warn(msg, e);
        }
        
    }
    
    @Override
    public boolean enable() {
        Log.setLogger(new OurLogger(getLogman()));
        if (helper == null) {
            Log.info("Dynmap is disabled (unsupported platform)");
            return false;
        }
        version = getVersion();

        /* Get MC version */
        String mcver = Canary.getServer().getServerVersion();

        /* Load extra biomes, if any */
        loadExtraBiomes(mcver);
             
        /* Set up player login/quit event handler */
        registerPlayerLoginListener();

        /* Get and initialize data folder */
        File dataDirectory = new File(Canary.getWorkingDirectory(), "config" + File.separator + "dynmap");
        if(dataDirectory.exists() == false)
            dataDirectory.mkdirs();
         
        /* Instantiate core */
        if(core == null)
            core = new DynmapCore();
        /* Inject dependencies */
        core.setPluginJarFile(new File(this.getPath()));
        core.setPluginVersion(version, "CanaryMod");
        core.setMinecraftVersion(mcver);
        core.setDataFolder(dataDirectory);
        if (server == null) {
            server = new CanaryServer();
        }
        
        core.setServer(server);
        core.setBlockNames(helper.getBlockShortNames());
        core.setBlockMaterialMap(helper.getBlockMaterialMap());
        core.setBiomeNames(helper.getBiomeNames());
        
        /* Load configuration */
        if(!core.initConfiguration(enabCoreCB)) {
            return false;
        }
        /* See if we need to wait before enabling core */
        if(!readyToEnable()) {
            Canary.hooks().registerListener(new OurPluginEnabledTrigger(), this);
        }
        else {
            doEnable();
        }
        // Start tps calculation
        perTickLimit = core.getMaxTickUseMS() * 1000000;

        Canary.hooks().registerListener(server, this);
        
        try {
            Canary.commands().registerCommands(new OurCommandHandler(), this, false);
        } catch (CommandDependencyException e) {
            Log.severe("Error registering commands", e);
        }
        
        return true;
    }
    
    private boolean readyToEnable() {
        return true;
    }
    
    private void doEnable() {
        /* Enable core */
        if(!core.enableCore(enabCoreCB)) {
            pm.disablePlugin("dynmap");
            return;
        }
        playerList = core.playerList;
        sscache = new SnapshotCache(core.getSnapShotCacheSize(), core.useSoftRefInSnapShotCache());

        /* Get map manager from core */
        mapManager = core.getMapManager();
        /* Initialized the currently loaded worlds */
        for (World world : Canary.getServer().getWorldManager().getAllWorlds()) {
            CanaryModWorld w = getWorld(world);
            if(core.processWorldLoad(w))    /* Have core process load first - fire event listeners if good load after */
                core.listenerManager.processWorldEvent(EventType.WORLD_LOAD, w);
        }    
        /* Register our update trigger events */
        registerEvents();

        /* Core is ready - notify API availability */
        DynmapCommonAPIListener.apiInitialized(this);

        Log.info("Enabled");
    }
    
    @Override
    public void disable() {
        /* Core is being disabled - notify API disable */
        DynmapCommonAPIListener.apiTerminated();
        
        /* Disable core */
        core.disableCore();

        if(sscache != null) {
            sscache.cleanup();
            sscache = null; 
        }
        Log.info("Disabled");
    }
    
    
    public class OurCommandHandler implements CommandListener {
        @Command(aliases = { "dynmap" },
                description = "Dynmap commands", permissions = { "" }, toolTip = "")
        public void dynmapCommand(MessageReceiver sender, String[] parameters) {
            DynmapCommandSender dsender;
            if(sender instanceof Player) {
                dsender = new BukkitPlayer((Player)sender);
            }
            else {
                dsender = new CanaryCommandSender(sender);
            }
            core.processCommand(dsender, "dynmap", parameters[0], Arrays.copyOfRange(parameters, 1, parameters.length));
        }
        @Command(aliases = { "dmarker" },
                description = "Dynmap marker commands", permissions = { "" }, toolTip = "")
        public void dmarkerCommand(MessageReceiver sender, String[] parameters) {
            DynmapCommandSender dsender;
            if(sender instanceof Player) {
                dsender = new BukkitPlayer((Player)sender);
            }
            else {
                dsender = new CanaryCommandSender(sender);
            }
            core.processCommand(dsender, "dmarker", parameters[0], Arrays.copyOfRange(parameters, 1, parameters.length));
        }
        
        @Command(aliases = { "dmap" },
                description = "Dynmap map commands", permissions = { "" }, toolTip = "")
        public void dmapCommand(MessageReceiver sender, String[] parameters) {
            DynmapCommandSender dsender;
            if(sender instanceof Player) {
                dsender = new BukkitPlayer((Player)sender);
            }
            else {
                dsender = new CanaryCommandSender(sender);
            }
            core.processCommand(dsender, "dmap", parameters[0], Arrays.copyOfRange(parameters, 1, parameters.length));
        }
    }
    
    @Override
    public final MarkerAPI getMarkerAPI() {
        return core.getMarkerAPI();
    }

    @Override
    public final boolean markerAPIInitialized() {
        return core.markerAPIInitialized();
    }

    @Override
    public final boolean sendBroadcastToWeb(String sender, String msg) {
        return core.sendBroadcastToWeb(sender, msg);
    }

    @Override
    public final int triggerRenderOfVolume(String wid, int minx, int miny, int minz,
            int maxx, int maxy, int maxz) {
        return core.triggerRenderOfVolume(wid, minx, miny, minz, maxx, maxy, maxz);
    }

    @Override
    public final int triggerRenderOfBlock(String wid, int x, int y, int z) {
        return core.triggerRenderOfBlock(wid, x, y, z);
    }

    @Override
    public final void setPauseFullRadiusRenders(boolean dopause) {
        core.setPauseFullRadiusRenders(dopause);
    }

    @Override
    public final boolean getPauseFullRadiusRenders() {
        return core.getPauseFullRadiusRenders();
    }

    @Override
    public final void setPauseUpdateRenders(boolean dopause) {
        core.setPauseUpdateRenders(dopause);
    }

    @Override
    public final boolean getPauseUpdateRenders() {
        return core.getPauseUpdateRenders();
    }

    @Override
    public final void setPlayerVisiblity(String player, boolean is_visible) {
        core.setPlayerVisiblity(player, is_visible);
    }

    @Override
    public final boolean getPlayerVisbility(String player) {
        return core.getPlayerVisbility(player);
    }

    @Override
    public final void postPlayerMessageToWeb(String playerid, String playerdisplay,
            String message) {
        core.postPlayerMessageToWeb(playerid, playerdisplay, message);
    }

    @Override
    public final void postPlayerJoinQuitToWeb(String playerid, String playerdisplay,
            boolean isjoin) {
        core.postPlayerJoinQuitToWeb(playerid, playerdisplay, isjoin);
    }

    @Override
    public final String getDynmapCoreVersion() {
        return core.getDynmapCoreVersion();
    }
    
    private static DynmapLocation toLoc(Location l) {
        return new DynmapLocation(DynmapWorld.normalizeWorldName(l.getWorld().getName()), l.getBlockX(), l.getBlockY(), l.getBlockZ());
    }
    
    private void registerPlayerLoginListener() {
        Canary.hooks().registerListener(new OurPlayerConnectionTrigger(), this);
    }

    private class BlockCheckHandler implements Runnable {
        public void run() {
            BlockToCheck btt;
            while(blocks_to_check.isEmpty() != true) {
                btt = blocks_to_check.pop();
                Location loc = btt.loc;
                World w = loc.getWorld();
                if(!w.isChunkLoaded(loc.getBlockX()>>4, loc.getBlockZ()>>4))
                    continue;
                Block b = w.getBlockAt(loc);
                int bt = b.getTypeId();
                /* Avoid stationary and moving water churn */
                if(bt == 9) bt = 8;
                if(btt.typeid == 9) btt.typeid = 8;
                if((bt != btt.typeid) || (btt.data != b.getData())) {
                    String wn = getWorld(w).getName();
                    sscache.invalidateSnapshot(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ());
                    mapManager.touch(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), btt.trigger);
                }
            }
            blocks_to_check = null;
            /* Kick next run, if one is needed */
            startIfNeeded();
        }
        public void startIfNeeded() {
            if((blocks_to_check == null) && (blocks_to_check_accum.isEmpty() == false)) { /* More pending? */
                blocks_to_check = blocks_to_check_accum;
                blocks_to_check_accum = new LinkedList<BlockToCheck>();
                server.scheduleServerTask(this, 10);
            }
        }
    }
    private BlockCheckHandler btth = new BlockCheckHandler();

    private void checkBlock(Block b, String trigger) {
        BlockToCheck btt = new BlockToCheck();
        btt.loc = b.getLocation();
        btt.typeid = b.getTypeId();
        btt.data = (byte) b.getData();
        btt.trigger = trigger;
        blocks_to_check_accum.add(btt); /* Add to accumulator */
        btth.startIfNeeded();
    }
    
    private boolean onplace;
    private boolean onbreak;
    private boolean onblockfromto;
    private boolean onblockphysics;
    private boolean onleaves;
    private boolean onburn;
    private boolean onpiston;
    private boolean onplayerjoin;
    private boolean onplayermove;
    private boolean ongeneratechunk;
    private boolean onexplosion;
    private boolean onstructuregrow;
    private boolean onblockgrow;
    private boolean onblockredstone;
    private boolean onblockupdate;
    private boolean onliquiddestroy;

    private void registerEvents() {
        
        // To trigger rendering.
        onplace = core.isTrigger("blockplaced");
        onbreak = core.isTrigger("blockbreak");
        onleaves = core.isTrigger("leavesdecay");
        onburn = core.isTrigger("blockburn");
        onblockfromto = core.isTrigger("blockfromto");
        onblockphysics = core.isTrigger("blockphysics");
        onpiston = core.isTrigger("pistonmoved");
        onblockredstone = core.isTrigger("blockredstone");
        onstructuregrow = core.isTrigger("structuregrow");
        onblockupdate = core.isTrigger("blockupdate");
        onliquiddestroy = core.isTrigger("liquiddestroy");
        onplayermove = core.isTrigger("playermove");
        onblockgrow = core.isTrigger("blockgrow");
        onplayerjoin = core.isTrigger("playerjoin");
        onexplosion = core.isTrigger("explosion");
        ongeneratechunk = core.isTrigger("chunkgenerated");
        
        if(onplace) {
            Canary.hooks().registerListener(new OurBlockPlaceTrigger(), this);
        }
        
        if(onbreak) {
            Canary.hooks().registerListener(new OurBlockBreakTrigger(), this);
        }
        
        if(onleaves) {
            Canary.hooks().registerListener(new OurLeavesDecayTrigger(), this);
        }

        if(onburn) {
            Canary.hooks().registerListener(new OurBlockBurnTrigger(), this);
        }
        
        if(onliquiddestroy) {
            Canary.hooks().registerListener(new OurLiquidDestroyTrigger(), this);
        }
        
        if(onblockphysics) {
            Canary.hooks().registerListener(new OurBlockPhysicsTrigger(), this);
        }
        
        if(onblockfromto) {
            Canary.hooks().registerListener(new OurBlockFromToTrigger(), this);
        }
        
        if(onpiston) {
            Canary.hooks().registerListener(new OurPistonTrigger(), this);
        }
        
        if(onblockgrow) {
            Canary.hooks().registerListener(new OurBlockGrowTrigger(), this);
        }
        
        if(onblockredstone) {
            Canary.hooks().registerListener(new OurRedstoneTrigger(), this);
        }
        
        /* Register player event trigger handlers */
        if (onplayerjoin) {
            Canary.hooks().registerListener(new OurPlayerJoinTrigger(), this);
        }

        /* Register block update handler */
        if (onblockupdate) {
            Canary.hooks().registerListener(new OurBlockUpdateTrigger(), this);
        }
        
        if(onplayermove) {
            Canary.hooks().registerListener(new OurPlayerMoveTrigger(), this);
            Log.warning("playermove trigger enabled - this trigger can cause excessive tile updating: use with caution");
        }
        /* Register entity event triggers */
        Canary.hooks().registerListener(new OurEntityTrigger(), this);
        
        // To link configuration to real loaded worlds.
        Canary.hooks().registerListener(new OurWorldTrigger(), this);

        if(ongeneratechunk) {
            Canary.hooks().registerListener(new OurChunkTrigger(), this);
        }
    }

    @Override
    public void assertPlayerInvisibility(String player, boolean is_invisible,
            String plugin_id) {
        core.assertPlayerInvisibility(player, is_invisible, plugin_id);
    }

    @Override
    public void assertPlayerVisibility(String player, boolean is_visible,
            String plugin_id) {
        core.assertPlayerVisibility(player, is_visible, plugin_id);
    }

    @Override
    public boolean setDisableChatToWebProcessing(boolean disable) {
        return core.setDisableChatToWebProcessing(disable);
    }
    @Override
    public boolean testIfPlayerVisibleToPlayer(String player, String player_to_see) {
        return core.testIfPlayerVisibleToPlayer(player, player_to_see);
    }
    @Override
    public boolean testIfPlayerInfoProtected() {
        return core.testIfPlayerInfoProtected();
    }
    @Override
    public void processSignChange(int blkid, String world, int x, int y, int z,
            String[] lines, String playerid) {
        core.processSignChange(blkid, world, x, y, z, lines, playerid);
    }
    
    /* Register world event triggers */
    public class OurWorldTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onWorldLoad(LoadWorldHook event) {
            CanaryModWorld w = getWorld(event.getWorld());
            if(core.processWorldLoad(w))    /* Have core process load first - fire event listeners if good load after */
                core.listenerManager.processWorldEvent(EventType.WORLD_LOAD, w);
        }
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onWorldUnload(UnloadWorldHook event) {
            CanaryModWorld w = getWorld(event.getWorld());
            if(w != null) {
                core.listenerManager.processWorldEvent(EventType.WORLD_UNLOAD, w);
                w.setWorldUnloaded();
                core.processWorldUnload(w);
            }
        }
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onStructureGrow(TreeGrowHook event) {
            if (onstructuregrow)
                checkBlock(event.getSapling(), "structuregrow");
        }

    }
    public class OurChunkTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onChunkPopulate(ChunkCreatedHook event) {
            Chunk c = event.getChunk();
            int maxy = 0;
            int[] hmap = c.getHeightMap();
            int[] hmap2 = c.getPrecipitationHeightMap();
            for (int i = 0; i < hmap.length; i++) {
                if (hmap[i] > maxy) maxy = hmap[i];
                if (hmap2[i] > maxy) maxy = hmap2[i];
            }
            /* Touch extreme corners */
            int x = c.getX() << 4;
            int z = c.getZ() << 4;
            mapManager.touchVolume(getWorld(event.getWorld()).getName(), x, 0, z, x+15, maxy, z+16, "chunkpopulate");
        }
    }
    public class OurEntityTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onEntityExplode(ExplosionHook event) {
            Location loc = event.getBlock().getLocation();
            String wname = getWorld(loc.getWorld()).getName();
            int minx, maxx, miny, maxy, minz, maxz;
            minx = maxx = loc.getBlockX();
            miny = maxy = loc.getBlockY();
            minz = maxz = loc.getBlockZ();
            /* Calculate volume impacted by explosion */
            List<Block> blocks = event.getAffectedBlocks();
            for(Block b: blocks) {
                Location l = b.getLocation();
                int x = l.getBlockX();
                if(x < minx) minx = x;
                if(x > maxx) maxx = x;
                int y = l.getBlockY();
                if(y < miny) miny = y;
                if(y > maxy) maxy = y;
                int z = l.getBlockZ();
                if(z < minz) minz = z;
                if(z > maxz) maxz = z;
            }
            sscache.invalidateSnapshot(wname, minx, miny, minz, maxx, maxy, maxz);
            if(onexplosion) {
                mapManager.touchVolume(wname, minx, miny, minz, maxx, maxy, maxz, "entityexplode");
            }
        }
    }
    public class OurPlayerMoveTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onPlayerMove(PlayerMoveHook event) {
            Location loc = event.getPlayer().getLocation();
            mapManager.touch(getWorld(loc.getWorld()).getName(), loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "playermove");
        }
    }
    public class OurPlayerJoinTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onPlayerJoin(ConnectionHook event) {
        
            Location loc = event.getPlayer().getLocation();
            mapManager.touch(getWorld(loc.getWorld()).getName(), loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "playerjoin");
        }
    }
    public class OurRedstoneTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockRedstone(RedstoneChangeHook event) {
            Location loc = event.getSourceBlock().getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            sscache.invalidateSnapshot(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ());
            mapManager.touch(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "blockredstone");
        }
    }
    public class OurBlockGrowTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockGrow(BlockGrowHook event) {
            Location loc = event.getGrowth().getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            sscache.invalidateSnapshot(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ());
            mapManager.touch(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "blockgrow");
        }
    }
    public class OurPistonTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockPistonRetract(PistonRetractHook event) {
            Block b = event.getPiston();
            Location loc = b.getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            int x = loc.getBlockX(), y = loc.getBlockY(), z = loc.getBlockZ();
            sscache.invalidateSnapshot(wn, x, y, z);
            if(onpiston)
                mapManager.touch(wn, x, y, z, "pistonretract");
            b = event.getMoving();
            if (b != null) {
                loc = b.getLocation();
                x = loc.getBlockX();
                y = loc.getBlockY();
                z = loc.getBlockZ();
                sscache.invalidateSnapshot(wn, x, y, z);
                if(onpiston)
                    mapManager.touch(wn, x, y, z, "pistonretract");
            }
        }

        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockPistonExtend(PistonExtendHook event) {
            Block b = event.getPiston();
            Location loc = b.getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            int x = loc.getBlockX(), y = loc.getBlockY(), z = loc.getBlockZ();
            sscache.invalidateSnapshot(wn, x, y, z);
            if(onpiston)
                mapManager.touch(wn, x, y, z, "pistonretract");
            b = event.getMoving();
            if (b != null) {
                loc = b.getLocation();
                x = loc.getBlockX();
                y = loc.getBlockY();
                z = loc.getBlockZ();
                sscache.invalidateSnapshot(wn, x, y, z);
                if(onpiston)
                    mapManager.touch(wn, x, y, z, "pistonretract");
            }
        }
    }
    public class OurBlockFromToTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockFromTo(FlowHook event) {
            Block b = event.getBlockFrom();
            BlockType m = b.getType();
            if((m != BlockType.WoodPlate) && (m != BlockType.StonePlate) && (m != null)) 
                checkBlock(b, "blockfromto");
            b = event.getBlockTo();
            m = b.getType();
            if((m != BlockType.WoodPlate) && (m != BlockType.StonePlate) && (m != null)) 
                checkBlock(b, "blockfromto");
        }
    }
    public class OurBlockPhysicsTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockPhysics(BlockPhysicsHook event) {
            Block b = event.getBlock();
            BlockType m = b.getType();
            if(m == null) return;
            if ((m == BlockType.WaterFlowing) || (m == BlockType.Water) ||
                    (m == BlockType.Lava) || (m == BlockType.LavaFlowing) ||
                    (m == BlockType.Gravel) || (m == BlockType.Sand)) {
                checkBlock(b, "blockphysics");
            }
        }
    }
    public class OurBlockBurnTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockBurn(IgnitionHook event) {
            IgnitionCause ic = event.getCause();
            if (ic == IgnitionCause.LAVA) {
                return;
            }
            Location loc = event.getBlock().getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            sscache.invalidateSnapshot(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ());
            if(onburn) {
                mapManager.touch(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "blockburn." + ic);
            }
        }
    }
    public class OurLeavesDecayTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onLeavesDecay(LeafDecayHook event) {
            Location loc = event.getBlock().getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            sscache.invalidateSnapshot(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ());
            mapManager.touch(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "leavesdecay");
        }
    }
    public class OurBlockBreakTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockBreak(BlockDestroyHook event) {
            Block b = event.getBlock();
            if(b == null) return;   /* Stupid mod workaround */
            Location loc = b.getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            sscache.invalidateSnapshot(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ());
            mapManager.touch(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "blockbreak");
        }
    }
    public class OurBlockPlaceTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onBlockPlace(BlockPlaceHook event) {
            Location loc = event.getBlockPlaced().getLocation();
            String wn = getWorld(loc.getWorld()).getName();
            sscache.invalidateSnapshot(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ());
            mapManager.touch(wn, loc.getBlockX(), loc.getBlockY(), loc.getBlockZ(), "blockplace");
        }
    }
    public class OurLiquidDestroyTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onLiquidDestroy(LiquidDestroyHook event) {
            checkBlock(event.getBlock(), "liquiddestroy");
        }
    }
    public class OurSignChangeTrigger implements PluginListener {
        @HookHandler(ignoreCanceled=true,priority=Priority.PASSIVE)
        public void onSignChange(SignChangeHook evt) {
            Sign s = evt.getSign();
            String[] lines = s.getText();    /* Note: changes to this change event - intentional */
            DynmapPlayer dp = null;
            Player p = evt.getPlayer();
            if(p != null) dp = new BukkitPlayer(p);
            core.listenerManager.processSignChangeEvent(EventType.SIGN_CHANGE, s.isSignPost()?63:68,
                getWorld(s.getWorld()).getName(), s.getX(), s.getY(), s.getZ(), lines, dp);
        }
    }
    public class OurBedLeaveTrigger implements PluginListener {
        @HookHandler(ignoreCanceled=true,priority=Priority.PASSIVE)
        public void onPlayerBedLeave(BedExitHook evt) {
            DynmapPlayer p = new BukkitPlayer(evt.getPlayer());
            core.listenerManager.processPlayerEvent(EventType.PLAYER_BED_LEAVE, p);
        }
    }
    public class OurPlayerChatTrigger implements PluginListener {
        @HookHandler(ignoreCanceled=true,priority=Priority.PASSIVE)
        public void onPlayerChat(ChatHook evt) {
            final Player p = evt.getPlayer();
            final String msg = evt.getMessage();
            ServerTaskManager.addTask(new ServerTask(DynmapPlugin.this, 1) {
                public void run() {
                    DynmapPlayer dp = null;
                    if(p != null)
                        dp = new BukkitPlayer(p);
                    core.listenerManager.processChatEvent(EventType.PLAYER_CHAT, dp, msg);
                }
            });
        }
    }
    public class OurPluginEnabledTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onPluginEnabled(PluginEnableHook evt) {
            if (!readyToEnable()) {
                if (readyToEnable()) { /* If we;re ready now, finish enable */
                    doEnable();   /* Finish enable */
                }
            }
        }
    }
    public class OurBreakTrigger implements PluginListener {
        @HookHandler(ignoreCanceled=true,priority=Priority.PASSIVE)
        public void onBlockBreak(BlockDestroyHook evt) {
            Block b = evt.getBlock();
            if(b == null) return;   /* Work around for stupid mods.... */
            Location l = b.getLocation();
            core.listenerManager.processBlockEvent(EventType.BLOCK_BREAK, b.getType().getId(),
                getWorld(l.getWorld()).getName(), l.getBlockX(), l.getBlockY(), l.getBlockZ());
        }
    }
    public class OurBlockUpdateTrigger implements PluginListener {
        @HookHandler(ignoreCanceled=true,priority=Priority.PASSIVE)
        public void onBlockUpdate(BlockUpdateHook evt) {
            checkBlock(evt.getBlock(), "blockupdate");
        }
    }
    public class OurPlayerConnectionTrigger implements PluginListener {
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onPlayerJoin(ConnectionHook evt) {
            final DynmapPlayer dp = new BukkitPlayer(evt.getPlayer());
            // Give other handlers a change to prep player (nicknames and such from Essentials)
            server.scheduleServerTask(new Runnable() {
                @Override
                public void run() {
                    core.listenerManager.processPlayerEvent(EventType.PLAYER_JOIN, dp);
                }
            }, 2);
        }
        @HookHandler(priority=Priority.PASSIVE, ignoreCanceled=true)
        public void onPlayerQuit(DisconnectionHook evt) {
            DynmapPlayer dp = new BukkitPlayer(evt.getPlayer());
            core.listenerManager.processPlayerEvent(EventType.PLAYER_QUIT, dp);
        }
    }
}
