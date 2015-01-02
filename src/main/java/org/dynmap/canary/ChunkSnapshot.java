package org.dynmap.canary;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import org.dynmap.Log;

import net.minecraft.nbt.NBTTagCompound;
import net.minecraft.nbt.NBTTagList;
import net.minecraft.world.chunk.Chunk;
import net.minecraft.world.chunk.NibbleArray;
import net.minecraft.world.chunk.storage.ExtendedBlockStorage;

/**
 * Represents a static, thread-safe snapshot of chunk of blocks
 * Purpose is to allow clean, efficient copy of a chunk data to be made, and then handed off for processing in another thread (e.g. map rendering)
 */
public class ChunkSnapshot
{
    private final int x, z;
    private final short[][] blockids; /* Block IDs, by section */
    private final byte[][] blockdata;
    private final byte[][] skylight;
    private final byte[][] emitlight;
    private final boolean[] empty;
    private final int[] hmap; // Height map
    private final byte[] biome;
    private final long captureFulltime;
    private final int sectionCnt;
    private final long inhabitedTicks;

    private static final int BLOCKS_PER_SECTION = 16 * 16 * 16;
    private static final int COLUMNS_PER_CHUNK = 16 * 16;
    private static final short[] emptyIDs = new short[BLOCKS_PER_SECTION];
    private static final byte[] emptyData = new byte[BLOCKS_PER_SECTION / 2];
    private static final byte[] fullData = new byte[BLOCKS_PER_SECTION / 2];
    private static Method getvalarray = null;

    static
    {
        for (int i = 0; i < fullData.length; i++)
        {
            fullData[i] = (byte)0xFF;
        }
        try {
            Method[] m = NibbleArray.class.getDeclaredMethods();
            for (Method mm : m) {
                if (mm.getName().equals("getValueArray")) {
                    getvalarray = mm;
                    break;
                }
            }
        } catch (Exception x) {
        }
    }

    /**
     * Construct empty chunk snapshot
     *
     * @param x
     * @param z
     */
    public ChunkSnapshot(int worldheight, int x, int z, long captime, long inhabitedTime)
    {
        this.x = x;
        this.z = z;
        this.captureFulltime = captime;
        this.biome = new byte[COLUMNS_PER_CHUNK];
        this.sectionCnt = worldheight / 16;
        /* Allocate arrays indexed by section */
        this.blockids = new short[this.sectionCnt][];
        this.blockdata = new byte[this.sectionCnt][];
        this.skylight = new byte[this.sectionCnt][];
        this.emitlight = new byte[this.sectionCnt][];
        this.empty = new boolean[this.sectionCnt];

        /* Fill with empty data */
        for (int i = 0; i < this.sectionCnt; i++)
        {
            this.empty[i] = true;
            this.blockids[i] = emptyIDs;
            this.blockdata[i] = emptyData;
            this.emitlight[i] = emptyData;
            this.skylight[i] = fullData;
        }

        /* Create empty height map */
        this.hmap = new int[16 * 16];
        
        this.inhabitedTicks = inhabitedTime;
    }

    public ChunkSnapshot(NBTTagCompound nbt, int worldheight) {
        this.x = nbt.f("xPos"); // getInteger
        this.z = nbt.f("zPos"); // getInteger
        this.captureFulltime = 0;
        this.hmap = nbt.l("HeightMap"); // getIntArray
        this.sectionCnt = worldheight / 16;
        if (nbt.c("InhabitedTime")) { // hasKey
            this.inhabitedTicks = nbt.g("InhabitedTime"); // getLong
        }
        else {
            this.inhabitedTicks = 0;
        }
        /* Allocate arrays indexed by section */
        this.blockids = new short[this.sectionCnt][];
        this.blockdata = new byte[this.sectionCnt][];
        this.skylight = new byte[this.sectionCnt][];
        this.emitlight = new byte[this.sectionCnt][];
        this.empty = new boolean[this.sectionCnt];
        /* Fill with empty data */
        for (int i = 0; i < this.sectionCnt; i++) {
            this.empty[i] = true;
            this.blockids[i] = emptyIDs;
            this.blockdata[i] = emptyData;
            this.emitlight[i] = emptyData;
            this.skylight[i] = fullData;
        }
        /* Get sections */
        NBTTagList sect = nbt.c("Sections", 10); // getTagList
        for (int i = 0; i < sect.c(); i++) { // tagCount
            NBTTagCompound sec = sect.b(i); // getCompoundTagAt
            byte secnum = sec.b("Y"); // getByte
            if (secnum >= this.sectionCnt) {
                Log.info("Section " + (int) secnum + " above world height " + worldheight);
                continue;
            }
            byte[] lsb_bytes = sec.k("Blocks"); // getByteArray
            short[] blkids = new short[BLOCKS_PER_SECTION];
            this.blockids[secnum] = blkids;
            int len = BLOCKS_PER_SECTION;
            if(len > lsb_bytes.length) len = lsb_bytes.length;
            for(int j = 0; j < len; j++) {
                blkids[j] = (short)(0xFF & lsb_bytes[j]); 
            }
            if (sec.c("Add")) { // hasKey    /* If additional data, add it */
                byte[] msb = sec.k("Add"); // getByteArray
                len = BLOCKS_PER_SECTION / 2;
                if(len > msb.length) len = msb.length;
                for (int j = 0; j < len; j++) {
                    short b = (short)(msb[j] & 0xFF);
                    if (b == 0) {
                        continue;
                    }
                    blkids[j << 1] |= (b & 0x0F) << 8;
                    blkids[(j << 1) + 1] |= (b & 0xF0) << 4;
                }
            }
            this.blockdata[secnum] = sec.k("Data"); // getByteArray
            this.emitlight[secnum] = sec.k("BlockLight"); // getByteArray
            if (sec.c("SkyLight")) {    // hasKey
                this.skylight[secnum] = sec.k("SkyLight"); // getByteArray
            }
            this.empty[secnum] = false;
        }
        /* Get biome data */
        if (nbt.c("Biomes")) { // hasKey
            this.biome = nbt.k("Biomes"); // getByteArray
        }
        else {
            this.biome = new byte[COLUMNS_PER_CHUNK];
        }
    }
    
    private static byte[] getValueArray(NibbleArray na) {
        if(getvalarray != null) {
            try {
                return (byte[])getvalarray.invoke(na);
            } catch (IllegalArgumentException e) {
            } catch (IllegalAccessException e) {
            } catch (InvocationTargetException e) {
            }
        }
        return na.a(); // getData
    }
    public ChunkSnapshot(Chunk chunk, int worldheight)
    {
        this(worldheight, chunk.a /*xPosition*/, chunk.b /* zPosition */, chunk.p().K() /*getWorld().getWorldTime() */, 
                chunk.w() /* getInhabitedTime() */);
        
        /* Copy biome data */
        System.arraycopy(chunk.k() /* getBiomeArray()*/, 0, biome, 0, COLUMNS_PER_CHUNK);
        ExtendedBlockStorage[] ebs = chunk.h() /* getBlockStorageArray() */;

        /* Copy sections */
        for (int i = 0; i < this.sectionCnt; i++)
        {
            ExtendedBlockStorage eb = (i < ebs.length) ? ebs[i] : null;

            if ((eb != null) && (eb.a() /*isEmpty()*/ == false))
            {
                this.empty[i] = false;
                /* Copy base IDs */
                /* Copy block data */
                byte[] blockd = new byte[BLOCKS_PER_SECTION / 2];
                short blockids[] = new short[BLOCKS_PER_SECTION];
                char[] blkd = eb.g(); // getData()
 
                for (int j = 0; j < BLOCKS_PER_SECTION; j++)
                {
                    blockids[j] = (short) (blkd[j] & 0xFFF);
                    blockd[j / 2] = (byte)(blockd[j / 2] | ((0xF & (blkd[j] >> 12)) << (4 * (j & 1))));
                }
                this.blockids[i] = blockids;
                this.blockdata[i] = blockd;
                /* Copy block lighting data */
                this.emitlight[i] = new byte[BLOCKS_PER_SECTION / 2];
                System.arraycopy(getValueArray(eb.h() /*getBlocklightArray()*/), 0, this.emitlight[i], 0, BLOCKS_PER_SECTION / 2);
                /* Copy sky lighting data */
                if(eb.i() /*getSkylightArray()*/ != null) {
                	this.skylight[i] = new byte[BLOCKS_PER_SECTION / 2];
                	System.arraycopy(getValueArray(eb.i() /*getSkylightArray()*/), 0, this.skylight[i], 0, BLOCKS_PER_SECTION / 2);
                }
                else {
                	this.skylight[i] = ChunkSnapshot.emptyData;
                }
            }
        }

        /* Save height map */
        System.arraycopy(chunk.q() /*getHeightMap()*/, 0, this.hmap, 0, hmap.length);
    }

    public int getX()
    {
        return x;
    }

    public int getZ()
    {
        return z;
    }

    public int getBlockTypeId(int x, int y, int z)
    {
        return blockids[y >> 4][((y & 0xF) << 8) | (z << 4) | x];
    }

    public int getBlockData(int x, int y, int z)
    {
        int off = ((y & 0xF) << 7) | (z << 3) | (x >> 1);
        return (blockdata[y >> 4][off] >> ((x & 1) << 2)) & 0xF;
    }

    public int getBlockSkyLight(int x, int y, int z)
    {
        int off = ((y & 0xF) << 7) | (z << 3) | (x >> 1);
        return (skylight[y >> 4][off] >> ((x & 1) << 2)) & 0xF;
    }

    public int getBlockEmittedLight(int x, int y, int z)
    {
        int off = ((y & 0xF) << 7) | (z << 3) | (x >> 1);
        return (emitlight[y >> 4][off] >> ((x & 1) << 2)) & 0xF;
    }

    public int getHighestBlockYAt(int x, int z)
    {
        return hmap[z << 4 | x];
    }

    public int getBiome(int x, int z)
    {
        return 255 & biome[z << 4 | x];
    }

    public final long getCaptureFullTime()
    {
        return captureFulltime;
    }

    public boolean isSectionEmpty(int sy)
    {
        return empty[sy];
    }
    
    public long getInhabitedTicks() {
        return inhabitedTicks;
    }
}
