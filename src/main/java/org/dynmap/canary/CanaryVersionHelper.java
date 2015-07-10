package org.dynmap.canary;

import java.util.ArrayList;
import java.util.List;

import net.canarymod.api.world.Biome;
import net.minecraft.block.Block;
import net.minecraft.block.material.Material;
import net.minecraft.world.biome.BiomeGenBase;

/**
 * Helper for isolation of canary version specific issues
 */
public class CanaryVersionHelper {

    private static CanaryVersionHelper helper = new CanaryVersionHelper();
    
    public static final CanaryVersionHelper getHelper() {
        return helper;
    }
    protected CanaryVersionHelper() {
        
    }
    /**
     * Get list of defined biomebase objects
     * @return biomes
     */
    public Biome[] getBiomeBaseList() {
        BiomeGenBase[] blist = BiomeGenBase.n();
        Biome[] rslt = new Biome[blist.length];
        for (int i = 0; i < blist.length; i++) {
            if (blist[i] == null) continue;
            rslt[i] = blist[i].getCanaryBiome();
        }
        return rslt;
    }
    /**
     * Get ID string from biomebase
     * @param bb - biome
     * @return biome name
     */
    public String getBiomeBaseIDString(Biome bb) {
        return ((net.canarymod.api.world.CanaryBiome)bb).getHandle().ah;
    }
    /**
     * Get block short name list
     * @return block names
     */
    public String[] getBlockShortNames() {
        String[] lst = new String[4096];
        for (int i = 0; i < 4096; i++) {
            Block b = Block.c(i);   // Get block
            if (b != null) {
                lst[i] = b.a();
                if (lst[i].startsWith("tile.")) {
                    lst[i] = lst[i].substring(5);
                }
            }
        }
        return lst;
    }
    /**
     * Get biome name list
     * @return biome names
     */
    public String[] getBiomeNames() {
        BiomeGenBase[] bb = BiomeGenBase.n();
        String[] lst = new String[256];
        for (int i = 0; i < 256; i++) {
            BiomeGenBase b = bb[i];
            if (b == null) continue;
            lst[i] = b.ah;
        }
        return lst;
    }
    /**
     * Get block material index list
     * @return index list
     */
    public int[] getBlockMaterialMap() {
        int[] lst = new int[4096];
        List<Material> byid = new ArrayList<Material>();
        for (int i = 0; i < 4096; i++) {
            Block b = Block.c(i);   // Get block
            if (b != null) {
                Material m = b.r();
                int idx = byid.indexOf(m);
                if (idx < 0) {
                    idx = byid.size();
                    byid.add(m);
                }
                lst[i] = idx;
            }
        }
        return lst;
    }
}
