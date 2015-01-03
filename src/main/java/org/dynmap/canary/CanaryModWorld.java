package org.dynmap.canary;
/**
 * Canary specific implementation of DynmapWorld
 */
import java.util.List;

import net.canarymod.api.world.DimensionType;
import net.canarymod.api.world.World;
import net.canarymod.api.world.position.Location;
import net.minecraft.util.BlockPos;
import net.minecraft.world.EnumSkyBlock;

import org.dynmap.DynmapChunk;
import org.dynmap.DynmapLocation;
import org.dynmap.DynmapWorld;
import org.dynmap.utils.MapChunkCache;

public class CanaryModWorld extends DynmapWorld {
    private World world;
    private net.minecraft.world.World nmsWorld;
    private DimensionType env;
    private boolean skylight;
    private DynmapLocation spawnloc = new DynmapLocation();
    
    public CanaryModWorld(World w) {
        this(w.getName(), w.getHeight(), 64, w.getType());
        setWorldLoaded(w);
        //new Permission("dynmap.world." + getName(), "Dynmap access for world " + getName(), PermissionDefault.OP);
    }
    public CanaryModWorld(String name, int height, int sealevel, DimensionType env) {
        super(name, height, sealevel);
        world = null;
        nmsWorld = null;
        this.env = env;
        skylight = (env == DimensionType.NORMAL);
        //new Permission("dynmap.world." + getName(), "Dynmap access for world " + getName(), PermissionDefault.OP);
        // Generate non-default environment lighting table
        if (env == DimensionType.NETHER) {
            float f = 0.1F;
            for (int i = 0; i <= 15; ++i) {
                float f1 = 1.0F - (float)i / 15.0F;
                this.setBrightnessTableEntry(i,  (1.0F - f1) / (f1 * 3.0F + 1.0F) * (1.0F - f) + f);
            }
        }
    }
    /**
     * Set world online
     * @param w - loaded world
     */
    public void setWorldLoaded(World w) {
        world = w;
        if (world instanceof net.canarymod.api.world.CanaryWorld) {
            nmsWorld = ((net.canarymod.api.world.CanaryWorld)w).getHandle();
        }
        env = world.getType();
        skylight = (env == DimensionType.NORMAL);
    }
    /**
     * Set world unloaded
     */
    @Override
    public void setWorldUnloaded() {
        getSpawnLocation(); /* Remember spawn location before unload */
        world = null;
        nmsWorld = null;
    }
    /* Test if world is nether */
    @Override
    public boolean isNether() {
        return env == DimensionType.NETHER;
    }
    /* Get world spawn location */
    @Override
    public DynmapLocation getSpawnLocation() {
        if(world != null) {
            Location sloc = world.getSpawnLocation();
            spawnloc.x = sloc.getBlockX();
            spawnloc.y = sloc.getBlockY();
            spawnloc.z = sloc.getBlockZ(); 
            spawnloc.world = normalizeWorldName(sloc.getWorld().getName());
        }
        return spawnloc;
    }
    /* Get world time */
    @Override
    public long getTime() {
        if(world != null) {
            return world.getRawTime();
        }
        else {
            return -1;
        }
    }
    /* World is storming */
    @Override
    public boolean hasStorm() {
        if(world != null) {
            return world.isRaining();
        }
        else {
            return false;
        }
    }
    /* World is thundering */
    @Override
    public boolean isThundering() {
        if(world != null) {
            return world.isThundering();
        }
        else {
            return false;
        }
    }
    /* World is loaded */
    @Override
    public boolean isLoaded() {
        return (world != null);
    }
    /* Get light level of block */
    @Override
    public int getLightLevel(int x, int y, int z) {
        if(world != null) {
            if ((y >= 0) && (y < this.worldheight)) {
                return world.getLightLevelAt(x, y, z);
            }
            return 0;
        }
        else {
            return -1;
        }
    }
    /* Get highest Y coord of given location */
    @Override
    public int getHighestBlockYAt(int x, int z) {
        if(world != null) {
            return world.getHighestBlockAt(x, z);
        }
        else {
            return -1;
        }
    }
    /* Test if sky light level is requestable */
    @Override
    public boolean canGetSkyLightLevel() {
        return skylight && (world != null);
    }
    /* Return sky light level */
    @Override
    public int getSkyLightLevel(int x, int y, int z) {
        if(nmsWorld != null) {
            if ((y >= 0) && (y < this.worldheight)) {
                return nmsWorld.b(EnumSkyBlock.SKY, new BlockPos(x, y, z));
            }
            else {
                return 15;
            }
        }
        else {
            return -1;
        }
    }
    /**
     * Get world environment ID (lower case - normal, the_end, nether)
     */
    @Override
    public String getEnvironment() {
        return env.getName().toLowerCase();
    }
    /**
     * Get map chunk cache for world
     */
    @Override
    public MapChunkCache getChunkCache(List<DynmapChunk> chunks) {
        if(isLoaded()) {
            CanaryModMapChunkCache c = new CanaryModMapChunkCache();
            c.setChunks(this, chunks);
            return c;
        }
        else {
            return null;
        }
    }
    
    public World getWorld() {
        return world;
    }
    public net.minecraft.world.World getNMSWorld() {
        return nmsWorld;
    }
}
