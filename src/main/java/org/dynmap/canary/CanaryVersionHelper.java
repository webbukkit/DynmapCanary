package org.dynmap.canary;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import net.canarymod.api.entity.living.humanoid.Player;
import net.minecraft.block.Block;
import net.minecraft.block.material.Material;
import net.minecraft.world.biome.BiomeGenBase;

import org.dynmap.Log;

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
     */
    public Object[] getBiomeBaseList() {
        return BiomeGenBase.n();
    }
    /** 
     * Get temperature from biomebase
     */
    public float getBiomeBaseTemperature(Object bb) {
        return ((BiomeGenBase)bb).ap;
    }
    /** 
     * Get humidity from biomebase
     */
    public float getBiomeBaseHumidity(Object bb) {
        return ((BiomeGenBase)bb).aq;
    }
    /**
     * Get ID string from biomebase
     */
    public String getBiomeBaseIDString(Object bb) {
        return ((BiomeGenBase)bb).ah;
    }
    /** 
     * Get ID from biomebase
     */
    public int getBiomeBaseID(Object bb) {
        return ((BiomeGenBase)bb).az;
    }
    /**
     * Get block short name list
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
