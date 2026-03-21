package zombie.iso;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.ObjectOutputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.nio.ByteBuffer;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Stack;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.Consumer;
import java.util.logging.Level;
import java.util.logging.Logger;
import se.krka.kahlua.vm.KahluaTable;
import zombie.GameTime;
import zombie.GameWindow;
import zombie.IndieGL;
import zombie.MapCollisionData;
import zombie.SandboxOptions;
import zombie.SoundManager;
import zombie.ZomboidBitFlag;
import zombie.Lua.LuaEventManager;
import zombie.Lua.LuaManager;
import zombie.ai.states.ZombieIdleState;
import zombie.audio.BaseSoundEmitter;
import zombie.characters.IsoGameCharacter;
import zombie.characters.IsoPlayer;
import zombie.characters.IsoSurvivor;
import zombie.characters.IsoZombie;
import zombie.characters.IsoGameCharacter.LightInfo;
import zombie.characters.Moodles.MoodleType;
import zombie.core.Color;
import zombie.core.Core;
import zombie.core.PerformanceSettings;
import zombie.core.Rand;
import zombie.core.SpriteRenderer;
import zombie.core.logger.ExceptionLogger;
import zombie.core.math.PZMath;
import zombie.core.network.ByteBufferWriter;
import zombie.core.opengl.Shader;
import zombie.core.properties.PropertyContainer;
import zombie.core.textures.ColorInfo;
import zombie.core.textures.Texture;
import zombie.core.textures.TextureDraw;
import zombie.debug.DebugLog;
import zombie.debug.DebugOptions;
import zombie.debug.DebugType;
import zombie.erosion.ErosionData.Square;
import zombie.erosion.categories.ErosionCategory.Data;
import zombie.inventory.InventoryItem;
import zombie.inventory.InventoryItemFactory;
import zombie.inventory.ItemContainer;
import zombie.inventory.types.Food;
import zombie.inventory.types.HandWeapon;
import zombie.iso.IsoGridSquare.1;
import zombie.iso.IsoGridSquare.CellGetSquare;
import zombie.iso.IsoGridSquare.CircleStencilShader;
import zombie.iso.IsoGridSquare.GetSquare;
import zombie.iso.IsoGridSquare.ILighting;
import zombie.iso.IsoGridSquare.Lighting;
import zombie.iso.IsoGridSquare.PuddlesDirection;
import zombie.iso.IsoGridSquare.s_performance;
import zombie.iso.IsoMetaGrid.Zone;
import zombie.iso.LightingJNI.JNILighting;
import zombie.iso.LosUtil.TestResults;
import zombie.iso.SpriteDetails.IsoFlagType;
import zombie.iso.SpriteDetails.IsoObjectType;
import zombie.iso.areas.IsoBuilding;
import zombie.iso.areas.IsoRoom;
import zombie.iso.areas.NonPvpZone;
import zombie.iso.areas.SafeHouse;
import zombie.iso.areas.isoregion.IsoRegions;
import zombie.iso.areas.isoregion.regions.IWorldRegion;
import zombie.iso.areas.isoregion.regions.IsoWorldRegion;
import zombie.iso.objects.IsoBarricade;
import zombie.iso.objects.IsoBrokenGlass;
import zombie.iso.objects.IsoCarBatteryCharger;
import zombie.iso.objects.IsoCompost;
import zombie.iso.objects.IsoCurtain;
import zombie.iso.objects.IsoDeadBody;
import zombie.iso.objects.IsoDoor;
import zombie.iso.objects.IsoFire;
import zombie.iso.objects.IsoFireManager;
import zombie.iso.objects.IsoGenerator;
import zombie.iso.objects.IsoLightSwitch;
import zombie.iso.objects.IsoMannequin;
import zombie.iso.objects.IsoRainSplash;
import zombie.iso.objects.IsoRaindrop;
import zombie.iso.objects.IsoThumpable;
import zombie.iso.objects.IsoTrap;
import zombie.iso.objects.IsoTree;
import zombie.iso.objects.IsoWaveSignal;
import zombie.iso.objects.IsoWindow;
import zombie.iso.objects.IsoWindowFrame;
import zombie.iso.objects.IsoWorldInventoryObject;
import zombie.iso.objects.RainManager;
import zombie.iso.objects.IsoTrap.ExplosionMode;
import zombie.iso.objects.interfaces.BarricadeAble;
import zombie.iso.sprite.IsoDirectionFrame;
import zombie.iso.sprite.IsoSprite;
import zombie.iso.sprite.IsoSpriteInstance;
import zombie.iso.sprite.IsoSpriteManager;
import zombie.iso.sprite.shapers.WallShaperN;
import zombie.iso.sprite.shapers.WallShaperW;
import zombie.iso.sprite.shapers.WallShaperWhole;
import zombie.network.GameClient;
import zombie.network.GameServer;
import zombie.network.ServerMap;
import zombie.network.ServerOptions;
import zombie.network.PacketTypes.PacketType;
import zombie.network.ServerLOS.ServerLighting;
import zombie.util.Type;
import zombie.util.io.BitHeader;
import zombie.util.io.BitHeaderWrite;
import zombie.util.io.BitHeader.HeaderSize;
import zombie.util.list.PZArrayList;
import zombie.util.list.PZArrayUtil;
import zombie.vehicles.BaseVehicle;
import zombie.vehicles.PolygonalMap2;

public final class IsoGridSquare {
    private boolean hasTree;
    private ArrayList<Float> LightInfluenceB;
    private ArrayList<Float> LightInfluenceG;
    private ArrayList<Float> LightInfluenceR;
    public final IsoGridSquare[] nav = new IsoGridSquare[8];
    public int collideMatrix = -1;
    public int pathMatrix = -1;
    public int visionMatrix = -1;
    public IsoRoom room = null;
    public IsoGridSquare w;
    public IsoGridSquare nw;
    public IsoGridSquare sw;
    public IsoGridSquare s;
    public IsoGridSquare n;
    public IsoGridSquare ne;
    public IsoGridSquare se;
    public IsoGridSquare e;
    public boolean haveSheetRope = false;
    private IWorldRegion isoWorldRegion;
    private boolean hasSetIsoWorldRegion = false;
    public int ObjectsSyncCount = 0;
    public IsoBuilding roofHideBuilding;
    public boolean bFlattenGrassEtc;
    private static final long VisiFlagTimerPeriod_ms = 750L;
    private final boolean[] playerCutawayFlags = new boolean[4];
    private final long[] playerCutawayFlagLockUntilTimes = new long[4];
    private final boolean[] targetPlayerCutawayFlags = new boolean[4];
    private final boolean[] playerIsDissolvedFlags = new boolean[4];
    private final long[] playerIsDissolvedFlagLockUntilTimes = new long[4];
    private final boolean[] targetPlayerIsDissolvedFlags = new boolean[4];
    private IsoWaterGeometry water = null;
    private IsoPuddlesGeometry puddles = null;
    private float puddlesCacheSize = -1.0F;
    private float puddlesCacheLevel = -1.0F;
    public final ILighting[] lighting = new ILighting[4];
    public int x;
    public int y;
    public int z;
    private int CachedScreenValue = -1;
    public float CachedScreenX;
    public float CachedScreenY;
    private static long torchTimer = 0L;
    public boolean SolidFloorCached = false;
    public boolean SolidFloor = false;
    private boolean CacheIsFree = false;
    private boolean CachedIsFree = false;
    public IsoChunk chunk;
    public int roomID = -1;
    public Integer ID = -999;
    public Zone zone;
    private final ArrayList<IsoGameCharacter> DeferedCharacters = new ArrayList<>();
    private int DeferredCharacterTick = -1;
    private final ArrayList<IsoMovingObject> StaticMovingObjects = new ArrayList<>(0);
    private final ArrayList<IsoMovingObject> MovingObjects = new ArrayList<>(0);
    protected final PZArrayList<IsoObject> Objects = new PZArrayList(IsoObject.class, 2);
    protected final PZArrayList<IsoObject> localTemporaryObjects = new PZArrayList(IsoObject.class, 2);
    private final ArrayList<IsoWorldInventoryObject> WorldObjects = new ArrayList<>();
    final ZomboidBitFlag hasTypes = new ZomboidBitFlag(IsoObjectType.MAX.index());
    private final PropertyContainer Properties = new PropertyContainer();
    private final ArrayList<IsoObject> SpecialObjects = new ArrayList<>(0);
    public boolean haveRoof = false;
    private boolean burntOut = false;
    private boolean bHasFlies = false;
    private IsoGridOcclusionData OcclusionDataCache = null;
    private static final PZArrayList<IsoWorldInventoryObject> tempWorldInventoryObjects = new PZArrayList(IsoWorldInventoryObject.class, 16);
    public static final ConcurrentLinkedQueue<IsoGridSquare> isoGridSquareCache = new ConcurrentLinkedQueue<>();
    public static ArrayDeque<IsoGridSquare> loadGridSquareCache;
    private boolean overlayDone = false;
    private KahluaTable table = null;
    private int trapPositionX = -1;
    private int trapPositionY = -1;
    private int trapPositionZ = -1;
    private boolean haveElectricity = false;
    public static int gridSquareCacheEmptyTimer = 0;
    private static float darkStep = 0.06F;
    public static int RecalcLightTime = 0;
    private static int lightcache = 0;
    public static final ArrayList<IsoGridSquare> choices = new ArrayList<>();
    public static boolean USE_WALL_SHADER = true;
    private static final int cutawayY = 0;
    private static final int cutawayNWWidth = 66;
    private static final int cutawayNWHeight = 226;
    private static final int cutawaySEXCut = 1084;
    private static final int cutawaySEXUncut = 1212;
    private static final int cutawaySEWidth = 6;
    private static final int cutawaySEHeight = 196;
    private static final int cutawayNXFullyCut = 700;
    private static final int cutawayNXCutW = 444;
    private static final int cutawayNXUncut = 828;
    private static final int cutawayNXCutE = 956;
    private static final int cutawayWXFullyCut = 512;
    private static final int cutawayWXCutS = 768;
    private static final int cutawayWXUncut = 896;
    private static final int cutawayWXCutN = 256;
    private static final int cutawayFenceXOffset = 1;
    private static final int cutawayLogWallXOffset = 1;
    private static final int cutawayMedicalCurtainWXOffset = -3;
    private static final int cutawaySpiffoWindowXOffset = -24;
    private static final int cutawayRoof4XOffset = -60;
    private static final int cutawayRoof17XOffset = -46;
    private static final int cutawayRoof28XOffset = -60;
    private static final int cutawayRoof41XOffset = -46;
    private static final ColorInfo lightInfoTemp = new ColorInfo();
    private static final float doorWindowCutawayLightMin = 0.3F;
    private static boolean bWallCutawayW;
    private static boolean bWallCutawayN;
    public boolean isSolidFloorCache;
    public boolean isExteriorCache;
    public boolean isVegitationCache;
    public int hourLastSeen = Integer.MIN_VALUE;
    static IsoGridSquare lastLoaded = null;
    public static int IDMax = -1;
    static int col = -1;
    static int path = -1;
    static int pathdoor = -1;
    static int vision = -1;
    public long hashCodeObjects;
    static final Color tr = new Color(1, 1, 1, 1);
    static final Color tl = new Color(1, 1, 1, 1);
    static final Color br = new Color(1, 1, 1, 1);
    static final Color bl = new Color(1, 1, 1, 1);
    static final Color interp1 = new Color(1, 1, 1, 1);
    static final Color interp2 = new Color(1, 1, 1, 1);
    static final Color finalCol = new Color(1, 1, 1, 1);
    public static final CellGetSquare cellGetSquare = new CellGetSquare();
    public boolean propertiesDirty = true;
    public static boolean UseSlowCollision = false;
    private static boolean bDoSlowPathfinding = false;
    private static final Comparator<IsoMovingObject> comp = (var0, var1) -> var0.compareToY(var1);
    public static boolean isOnScreenLast = false;
    private float splashX;
    private float splashY;
    private float splashFrame = -1.0F;
    private int splashFrameNum;
    private final ColorInfo[] lightInfo = new ColorInfo[4];
    static String[] rainsplashCache = new String[50];
    private static final ColorInfo defColorInfo = new ColorInfo();
    private static final ColorInfo blackColorInfo = new ColorInfo();
    static int colu = 0;
    static int coll = 0;
    static int colr = 0;
    static int colu2 = 0;
    static int coll2 = 0;
    static int colr2 = 0;
    public static boolean CircleStencil = false;
    public static float rmod = 0.0F;
    public static float gmod = 0.0F;
    public static float bmod = 0.0F;
    static final Vector2 tempo = new Vector2();
    static final Vector2 tempo2 = new Vector2();
    private IsoRaindrop RainDrop = null;
    private IsoRainSplash RainSplash = null;
    private Square erosion;
    private static final int[] SURFACE_OFFSETS = new int[8];
    public static final int WALL_TYPE_N = 1;
    public static final int WALL_TYPE_S = 2;
    public static final int WALL_TYPE_W = 4;
    public static final int WALL_TYPE_E = 8;

    public static boolean getMatrixBit(int var0, int var1, int var2, int var3) {
        return getMatrixBit(var0, (byte)var1, (byte)var2, (byte)var3);
    }

    public static boolean getMatrixBit(int var0, byte var1, byte var2, byte var3) {
        return (var0 >> var1 + var2 * 3 + var3 * 9 & 1) != 0;
    }

    public static int setMatrixBit(int var0, int var1, int var2, int var3, boolean var4) {
        return setMatrixBit(var0, (byte)var1, (byte)var2, (byte)var3, var4);
    }

    public static int setMatrixBit(int var0, byte var1, byte var2, byte var3, boolean var4) {
        if (var4) {
            return var0 | 1 << var1 + var2 * 3 + var3 * 9;
        } else {
            return var0 & ~(1 << var1 + var2 * 3 + var3 * 9);
        }
    }

    public void setPlayerCutawayFlag(int var1, boolean var2, long var3) {
        this.targetPlayerCutawayFlags[var1] = var2;
        if (var3 > this.playerCutawayFlagLockUntilTimes[var1] && this.playerCutawayFlags[var1] != this.targetPlayerCutawayFlags[var1]) {
            this.playerCutawayFlags[var1] = this.targetPlayerCutawayFlags[var1];
            this.playerCutawayFlagLockUntilTimes[var1] = var3 + 750L;
        }
    }

    public boolean getPlayerCutawayFlag(int var1, long var2) {
        if (var2 > this.playerCutawayFlagLockUntilTimes[var1]) {
            return this.targetPlayerCutawayFlags[var1];
        } else {
            return this.playerCutawayFlags[var1];
        }
    }

    public void setIsDissolved(int var1, boolean var2, long var3) {
        this.targetPlayerIsDissolvedFlags[var1] = var2;
        if (var3 > this.playerIsDissolvedFlagLockUntilTimes[var1] && this.playerIsDissolvedFlags[var1] != this.targetPlayerIsDissolvedFlags[var1]) {
            this.playerIsDissolvedFlags[var1] = this.targetPlayerIsDissolvedFlags[var1];
            this.playerIsDissolvedFlagLockUntilTimes[var1] = var3 + 750L;
        }
    }

    public boolean getIsDissolved(int var1, long var2) {
        if (var2 > this.playerIsDissolvedFlagLockUntilTimes[var1]) {
            return this.targetPlayerIsDissolvedFlags[var1];
        } else {
            return this.playerIsDissolvedFlags[var1];
        }
    }

    public IsoWaterGeometry getWater() {
        label26:
        if (this.water != null && this.water.m_adjacentChunkLoadedCounter != this.chunk.m_adjacentChunkLoadedCounter) {
            this.water.m_adjacentChunkLoadedCounter = this.chunk.m_adjacentChunkLoadedCounter;
            if (!this.water.hasWater && !this.water.bShore) {
                break label26;
            }

            this.clearWater();
        }

        if (this.water == null) {
            try {
                this.water = (IsoWaterGeometry)IsoWaterGeometry.pool.alloc();
                this.water.m_adjacentChunkLoadedCounter = this.chunk.m_adjacentChunkLoadedCounter;
                if (this.water.init(this) == null) {
                    IsoWaterGeometry.pool.release(this.water);
                    this.water = null;
                }
            } catch (Exception var2) {
                this.clearWater();
            }
        }

        return this.water;
    }

    public void clearWater() {
        if (this.water != null) {
            IsoWaterGeometry.pool.release(this.water);
            this.water = null;
        }
    }

    public IsoPuddlesGeometry getPuddles() {
        if (this.puddles == null) {
            try {
                synchronized (IsoPuddlesGeometry.pool) {
                    this.puddles = (IsoPuddlesGeometry)IsoPuddlesGeometry.pool.alloc();
                }
            } catch (Exception var4) {
                this.clearPuddles();
            }
        }

        return this.puddles;
    }

    public void clearPuddles() {
        if (this.puddles != null) {
            this.puddles.square = null;
            synchronized (IsoPuddlesGeometry.pool) {
                IsoPuddlesGeometry.pool.release(this.puddles);
            }
        }
    }

    public float getPuddlesInGround() {
        if (this.isInARoom()) {
            return -1.0F;
        } else {
            if ((double)Math.abs(
                    IsoPuddles.getInstance().getPuddlesSize()
                        + (float)Core.getInstance().getPerfPuddles()
                        + (float)IsoCamera.frameState.OffscreenWidth
                        - this.puddlesCacheSize
                )
                > 0.01) {
                this.puddlesCacheSize = IsoPuddles.getInstance().getPuddlesSize()
                    + (float)Core.getInstance().getPerfPuddles()
                    + (float)IsoCamera.frameState.OffscreenWidth;
                this.puddlesCacheLevel = IsoPuddlesCompute.computePuddle(this);
            }

            return this.puddlesCacheLevel;
        }
    }

    public IsoGridOcclusionData getOcclusionData() {
        return this.OcclusionDataCache;
    }

    public IsoGridOcclusionData getOrCreateOcclusionData() {
        assert !GameServer.bServer;

        if (this.OcclusionDataCache == null) {
            this.OcclusionDataCache = new IsoGridOcclusionData(this);
        }

        return this.OcclusionDataCache;
    }

    public void softClear() {
        this.zone = null;
        this.room = null;
        this.w = null;
        this.nw = null;
        this.sw = null;
        this.s = null;
        this.n = null;
        this.ne = null;
        this.se = null;
        this.e = null;
        this.isoWorldRegion = null;
        this.hasSetIsoWorldRegion = false;

        for (int var1 = 0; var1 < 8; var1++) {
            this.nav[var1] = null;
        }
    }

    public float getGridSneakModifier(boolean var1) {
        if (!var1) {
            if (this.Properties.Is("CloseSneakBonus")) {
                return (float)Integer.parseInt(this.Properties.Val("CloseSneakBonus")) / 100.0F;
            }

            if (this.Properties.Is(IsoFlagType.collideN)
                || this.Properties.Is(IsoFlagType.collideW)
                || this.Properties.Is(IsoFlagType.WindowN)
                || this.Properties.Is(IsoFlagType.WindowW)
                || this.Properties.Is(IsoFlagType.doorN)
                || this.Properties.Is(IsoFlagType.doorW)) {
                return 8.0F;
            }
        } else if (this.Properties.Is(IsoFlagType.solidtrans)) {
            return 4.0F;
        }

        return 0.0F;
    }

    public boolean isSomethingTo(IsoGridSquare var1) {
        return this.isWallTo(var1) || this.isWindowTo(var1) || this.isDoorTo(var1);
    }

    public IsoObject getTransparentWallTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this && this.isWallTo(var1)) {
            if (var1.x > this.x && var1.Properties.Is(IsoFlagType.SpearOnlyAttackThrough) && !var1.Properties.Is(IsoFlagType.WindowW)) {
                return var1.getWall();
            } else if (this.x > var1.x && this.Properties.Is(IsoFlagType.SpearOnlyAttackThrough) && !this.Properties.Is(IsoFlagType.WindowW)) {
                return this.getWall();
            } else if (var1.y > this.y && var1.Properties.Is(IsoFlagType.SpearOnlyAttackThrough) && !var1.Properties.Is(IsoFlagType.WindowN)) {
                return var1.getWall();
            } else if (this.y > var1.y && this.Properties.Is(IsoFlagType.SpearOnlyAttackThrough) && !this.Properties.Is(IsoFlagType.WindowN)) {
                return this.getWall();
            } else {
                if (var1.x != this.x && var1.y != this.y) {
                    IsoObject var2 = this.getTransparentWallTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z));
                    IsoObject var3 = this.getTransparentWallTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z));
                    if (var2 != null) {
                        return var2;
                    }

                    if (var3 != null) {
                        return var3;
                    }

                    var2 = var1.getTransparentWallTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z));
                    var3 = var1.getTransparentWallTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z));
                    if (var2 != null) {
                        return var2;
                    }

                    if (var3 != null) {
                        return var3;
                    }
                }

                return null;
            }
        } else {
            return null;
        }
    }

    public boolean isWallTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            if (var1.x > this.x && var1.Properties.Is(IsoFlagType.collideW) && !var1.Properties.Is(IsoFlagType.WindowW)) {
                return true;
            } else if (this.x > var1.x && this.Properties.Is(IsoFlagType.collideW) && !this.Properties.Is(IsoFlagType.WindowW)) {
                return true;
            } else if (var1.y > this.y && var1.Properties.Is(IsoFlagType.collideN) && !var1.Properties.Is(IsoFlagType.WindowN)) {
                return true;
            } else if (this.y > var1.y && this.Properties.Is(IsoFlagType.collideN) && !this.Properties.Is(IsoFlagType.WindowN)) {
                return true;
            } else {
                if (var1.x != this.x && var1.y != this.y) {
                    if (this.isWallTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                        || this.isWallTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                        return true;
                    }

                    if (var1.isWallTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                        || var1.isWallTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                        return true;
                    }
                }

                return false;
            }
        } else {
            return false;
        }
    }

    public boolean isWindowTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            if (var1.x > this.x && var1.Properties.Is(IsoFlagType.windowW)) {
                return true;
            } else if (this.x > var1.x && this.Properties.Is(IsoFlagType.windowW)) {
                return true;
            } else if (var1.y > this.y && var1.Properties.Is(IsoFlagType.windowN)) {
                return true;
            } else if (this.y > var1.y && this.Properties.Is(IsoFlagType.windowN)) {
                return true;
            } else {
                if (var1.x != this.x && var1.y != this.y) {
                    if (this.isWindowTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                        || this.isWindowTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                        return true;
                    }

                    if (var1.isWindowTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                        || var1.isWindowTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                        return true;
                    }
                }

                return false;
            }
        } else {
            return false;
        }
    }

    public boolean haveDoor() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            if (this.Objects.get(var1) instanceof IsoDoor) {
                return true;
            }
        }

        return false;
    }

    public boolean hasDoorOnEdge(IsoDirections var1, boolean var2) {
        for (int var3 = 0; var3 < this.SpecialObjects.size(); var3++) {
            IsoDoor var4 = (IsoDoor)Type.tryCastTo(this.SpecialObjects.get(var3), IsoDoor.class);
            if (var4 != null && var4.getSpriteEdge(var2) == var1) {
                return true;
            }

            IsoThumpable var5 = (IsoThumpable)Type.tryCastTo(this.SpecialObjects.get(var3), IsoThumpable.class);
            if (var5 != null && var5.getSpriteEdge(var2) == var1) {
                return true;
            }
        }

        return false;
    }

    public boolean hasClosedDoorOnEdge(IsoDirections var1) {
        boolean var2 = false;

        for (int var3 = 0; var3 < this.SpecialObjects.size(); var3++) {
            IsoDoor var4 = (IsoDoor)Type.tryCastTo(this.SpecialObjects.get(var3), IsoDoor.class);
            if (var4 != null && !var4.IsOpen() && var4.getSpriteEdge(var2) == var1) {
                return true;
            }

            IsoThumpable var5 = (IsoThumpable)Type.tryCastTo(this.SpecialObjects.get(var3), IsoThumpable.class);
            if (var5 != null && !var5.IsOpen() && var5.getSpriteEdge(var2) == var1) {
                return true;
            }
        }

        return false;
    }

    public boolean hasOpenDoorOnEdge(IsoDirections var1) {
        boolean var2 = false;

        for (int var3 = 0; var3 < this.SpecialObjects.size(); var3++) {
            IsoDoor var4 = (IsoDoor)Type.tryCastTo(this.SpecialObjects.get(var3), IsoDoor.class);
            if (var4 != null && var4.IsOpen() && var4.getSpriteEdge(var2) == var1) {
                return true;
            }

            IsoThumpable var5 = (IsoThumpable)Type.tryCastTo(this.SpecialObjects.get(var3), IsoThumpable.class);
            if (var5 != null && var5.IsOpen() && var5.getSpriteEdge(var2) == var1) {
                return true;
            }
        }

        return false;
    }

    public boolean isDoorTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            if (var1.x > this.x && var1.Properties.Is(IsoFlagType.doorW)) {
                return true;
            } else if (this.x > var1.x && this.Properties.Is(IsoFlagType.doorW)) {
                return true;
            } else if (var1.y > this.y && var1.Properties.Is(IsoFlagType.doorN)) {
                return true;
            } else if (this.y > var1.y && this.Properties.Is(IsoFlagType.doorN)) {
                return true;
            } else {
                if (var1.x != this.x && var1.y != this.y) {
                    if (this.isDoorTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                        || this.isDoorTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                        return true;
                    }

                    if (var1.isDoorTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                        || var1.isDoorTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                        return true;
                    }
                }

                return false;
            }
        } else {
            return false;
        }
    }

    public boolean isBlockedTo(IsoGridSquare var1) {
        return this.isWallTo(var1) || this.isWindowBlockedTo(var1) || this.isDoorBlockedTo(var1);
    }

    public boolean isWindowBlockedTo(IsoGridSquare var1) {
        if (var1 == null) {
            return false;
        } else if (var1.x > this.x && var1.hasBlockedWindow(false)) {
            return true;
        } else if (this.x > var1.x && this.hasBlockedWindow(false)) {
            return true;
        } else if (var1.y > this.y && var1.hasBlockedWindow(true)) {
            return true;
        } else if (this.y > var1.y && this.hasBlockedWindow(true)) {
            return true;
        } else {
            if (var1.x != this.x && var1.y != this.y) {
                if (this.isWindowBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                    || this.isWindowBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                    return true;
                }

                if (var1.isWindowBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                    || var1.isWindowBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                    return true;
                }
            }

            return false;
        }
    }

    public boolean hasBlockedWindow(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (var3 instanceof IsoWindow var4 && var4.getNorth() == var1) {
                return !var4.isDestroyed() && !var4.open || var4.isBarricaded();
            }
        }

        return false;
    }

    public boolean isDoorBlockedTo(IsoGridSquare var1) {
        if (var1 == null) {
            return false;
        } else if (var1.x > this.x && var1.hasBlockedDoor(false)) {
            return true;
        } else if (this.x > var1.x && this.hasBlockedDoor(false)) {
            return true;
        } else if (var1.y > this.y && var1.hasBlockedDoor(true)) {
            return true;
        } else if (this.y > var1.y && this.hasBlockedDoor(true)) {
            return true;
        } else {
            if (var1.x != this.x && var1.y != this.y) {
                if (this.isDoorBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                    || this.isDoorBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                    return true;
                }

                if (var1.isDoorBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(var1.x, this.y, this.z))
                    || var1.isDoorBlockedTo(IsoWorld.instance.CurrentCell.getGridSquare(this.x, var1.y, this.z))) {
                    return true;
                }
            }

            return false;
        }
    }

    public boolean hasBlockedDoor(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (var3 instanceof IsoDoor var4 && var4.getNorth() == var1) {
                return !var4.open || var4.isBarricaded();
            }

            if (var3 instanceof IsoThumpable var5 && var5.isDoor() && var5.getNorth() == var1) {
                return !var5.open || var5.isBarricaded();
            }
        }

        return false;
    }

    public IsoCurtain getCurtain(IsoObjectType var1) {
        for (int var2 = 0; var2 < this.getSpecialObjects().size(); var2++) {
            IsoCurtain var3 = (IsoCurtain)Type.tryCastTo(this.getSpecialObjects().get(var2), IsoCurtain.class);
            if (var3 != null && var3.getType() == var1) {
                return var3;
            }
        }

        return null;
    }

    public IsoObject getHoppable(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            PropertyContainer var4 = var3.getProperties();
            if (var4 != null && var4.Is(var1 ? IsoFlagType.HoppableN : IsoFlagType.HoppableW)) {
                return var3;
            }

            if (var4 != null && var4.Is(var1 ? IsoFlagType.WindowN : IsoFlagType.WindowW)) {
                return var3;
            }
        }

        return null;
    }

    public IsoObject getHoppableTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            if (var1.x < this.x && var1.y == this.y) {
                IsoObject var2 = this.getHoppable(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x == this.x && var1.y < this.y) {
                IsoObject var5 = this.getHoppable(true);
                if (var5 != null) {
                    return var5;
                }
            }

            if (var1.x > this.x && var1.y == this.y) {
                IsoObject var6 = var1.getHoppable(false);
                if (var6 != null) {
                    return var6;
                }
            }

            if (var1.x == this.x && var1.y > this.y) {
                IsoObject var7 = var1.getHoppable(true);
                if (var7 != null) {
                    return var7;
                }
            }

            if (var1.x != this.x && var1.y != this.y) {
                IsoGridSquare var3 = this.getCell().getGridSquare(this.x, var1.y, this.z);
                IsoGridSquare var4 = this.getCell().getGridSquare(var1.x, this.y, this.z);
                IsoObject var8 = this.getHoppableTo(var3);
                if (var8 != null) {
                    return var8;
                }

                var8 = this.getHoppableTo(var4);
                if (var8 != null) {
                    return var8;
                }

                var8 = var1.getHoppableTo(var3);
                if (var8 != null) {
                    return var8;
                }

                var8 = var1.getHoppableTo(var4);
                if (var8 != null) {
                    return var8;
                }
            }

            return null;
        } else {
            return null;
        }
    }

    public boolean isHoppableTo(IsoGridSquare var1) {
        if (var1 == null) {
            return false;
        } else if (var1.x != this.x && var1.y != this.y) {
            return false;
        } else if (var1.x > this.x && var1.Properties.Is(IsoFlagType.HoppableW)) {
            return true;
        } else if (this.x > var1.x && this.Properties.Is(IsoFlagType.HoppableW)) {
            return true;
        } else if (var1.y > this.y && var1.Properties.Is(IsoFlagType.HoppableN)) {
            return true;
        } else if (this.y > var1.y && this.Properties.Is(IsoFlagType.HoppableN)) {
            return true;
        } else {
            return false;
        }
    }

    public void discard() {
        this.hourLastSeen = -32768;
        this.chunk = null;
        this.zone = null;
        this.LightInfluenceB = null;
        this.LightInfluenceG = null;
        this.LightInfluenceR = null;
        this.room = null;
        this.w = null;
        this.nw = null;
        this.sw = null;
        this.s = null;
        this.n = null;
        this.ne = null;
        this.se = null;
        this.e = null;
        this.isoWorldRegion = null;
        this.hasSetIsoWorldRegion = false;
        this.nav[0] = null;
        this.nav[1] = null;
        this.nav[2] = null;
        this.nav[3] = null;
        this.nav[4] = null;
        this.nav[5] = null;
        this.nav[6] = null;
        this.nav[7] = null;

        for (int var1 = 0; var1 < 4; var1++) {
            if (this.lighting[var1] != null) {
                this.lighting[var1].reset();
            }
        }

        this.SolidFloorCached = false;
        this.SolidFloor = false;
        this.CacheIsFree = false;
        this.CachedIsFree = false;
        this.chunk = null;
        this.roomID = -1;
        this.DeferedCharacters.clear();
        this.DeferredCharacterTick = -1;
        this.StaticMovingObjects.clear();
        this.MovingObjects.clear();
        this.Objects.clear();
        this.WorldObjects.clear();
        this.hasTypes.clear();
        this.table = null;
        this.Properties.Clear();
        this.SpecialObjects.clear();
        this.RainDrop = null;
        this.RainSplash = null;
        this.overlayDone = false;
        this.haveRoof = false;
        this.burntOut = false;
        this.trapPositionX = this.trapPositionY = this.trapPositionZ = -1;
        this.haveElectricity = false;
        this.haveSheetRope = false;
        if (this.erosion != null) {
            this.erosion.reset();
        }

        if (this.OcclusionDataCache != null) {
            this.OcclusionDataCache.Reset();
        }

        this.roofHideBuilding = null;
        this.bHasFlies = false;
        isoGridSquareCache.add(this);
    }

    private static boolean validateUser(String var0, String var1) throws MalformedURLException, IOException {
        URL var2 = new URL("http://www.projectzomboid.com/scripts/auth.php?username=" + var0 + "&password=" + var1);
        URLConnection var3 = var2.openConnection();
        BufferedReader var4 = new BufferedReader(new InputStreamReader(var3.getInputStream()));

        String var5;
        while ((var5 = var4.readLine()) != null) {
            if (var5.contains("success")) {
                return true;
            }
        }

        return false;
    }

    public float DistTo(int var1, int var2) {
        return IsoUtils.DistanceManhatten((float)var1 + 0.5F, (float)var2 + 0.5F, (float)this.x, (float)this.y);
    }

    public float DistTo(IsoGridSquare var1) {
        return IsoUtils.DistanceManhatten((float)this.x + 0.5F, (float)this.y + 0.5F, (float)var1.x + 0.5F, (float)var1.y + 0.5F);
    }

    public float DistToProper(IsoGridSquare var1) {
        return IsoUtils.DistanceTo((float)this.x + 0.5F, (float)this.y + 0.5F, (float)var1.x + 0.5F, (float)var1.y + 0.5F);
    }

    public float DistTo(IsoMovingObject var1) {
        return IsoUtils.DistanceManhatten((float)this.x + 0.5F, (float)this.y + 0.5F, var1.getX(), var1.getY());
    }

    public float DistToProper(IsoMovingObject var1) {
        return IsoUtils.DistanceTo((float)this.x + 0.5F, (float)this.y + 0.5F, var1.getX(), var1.getY());
    }

    public boolean isSafeToSpawn() {
        choices.clear();
        this.isSafeToSpawn(this, 0);
        if (choices.size() > 7) {
            choices.clear();
            return true;
        } else {
            choices.clear();
            return false;
        }
    }

    public void isSafeToSpawn(IsoGridSquare var1, int var2) {
        if (var2 <= 5) {
            choices.add(var1);
            if (var1.n != null && !choices.contains(var1.n)) {
                this.isSafeToSpawn(var1.n, var2 + 1);
            }

            if (var1.s != null && !choices.contains(var1.s)) {
                this.isSafeToSpawn(var1.s, var2 + 1);
            }

            if (var1.e != null && !choices.contains(var1.e)) {
                this.isSafeToSpawn(var1.e, var2 + 1);
            }

            if (var1.w != null && !choices.contains(var1.w)) {
                this.isSafeToSpawn(var1.w, var2 + 1);
            }
        }
    }

    public static boolean auth(String var0, char[] var1) {
        if (var0.length() > 64) {
            return false;
        } else {
            String var2 = var1.toString();
            if (var2.length() > 64) {
                return false;
            } else {
                try {
                    return validateUser(var0, var2);
                } catch (MalformedURLException var4) {
                    Logger.getLogger(IsoGridSquare.class.getName()).log(Level.SEVERE, null, var4);
                } catch (IOException var5) {
                    Logger.getLogger(IsoGridSquare.class.getName()).log(Level.SEVERE, null, var5);
                }
            }
        }

        return false;
    }

    private void renderAttachedSpritesWithNoWallLighting(IsoObject var1, ColorInfo var2) {
        if (var1.AttachedAnimSprite != null && !var1.AttachedAnimSprite.isEmpty()) {
            boolean var3 = false;

            for (int var4 = 0; var4 < var1.AttachedAnimSprite.size(); var4++) {
                IsoSpriteInstance var5 = (IsoSpriteInstance)var1.AttachedAnimSprite.get(var4);
                if (var5.parentSprite != null && var5.parentSprite.Properties.Is(IsoFlagType.NoWallLighting)) {
                    var3 = true;
                    break;
                }
            }

            if (var3) {
                defColorInfo.r = var2.r;
                defColorInfo.g = var2.g;
                defColorInfo.b = var2.b;
                float var7 = defColorInfo.a;
                if (CircleStencil) {
                }

                for (int var8 = 0; var8 < var1.AttachedAnimSprite.size(); var8++) {
                    IsoSpriteInstance var6 = (IsoSpriteInstance)var1.AttachedAnimSprite.get(var8);
                    if (var6.parentSprite != null && var6.parentSprite.Properties.Is(IsoFlagType.NoWallLighting)) {
                        defColorInfo.a = var6.alpha;
                        var6.render(
                            var1,
                            (float)this.x,
                            (float)this.y,
                            (float)this.z,
                            var1.dir,
                            var1.offsetX,
                            var1.offsetY + var1.getRenderYOffset() * (float)Core.TileScale,
                            defColorInfo
                        );
                        var6.update();
                    }
                }

                defColorInfo.r = 1.0F;
                defColorInfo.g = 1.0F;
                defColorInfo.b = 1.0F;
                defColorInfo.a = var7;
            }
        }
    }

    public void DoCutawayShader(
        IsoObject var1,
        IsoDirections var2,
        boolean var3,
        boolean var4,
        boolean var5,
        boolean var6,
        boolean var7,
        boolean var8,
        boolean var9,
        WallShaperWhole var10
    ) {
        Texture var11 = Texture.getSharedTexture("media/wallcutaways.png");
        if (var11 != null && var11.getID() != -1) {
            boolean var12 = var1.sprite.getProperties().Is(IsoFlagType.NoWallLighting);
            int var13 = IsoCamera.frameState.playerIndex;
            ColorInfo var14 = this.lightInfo[var13];
            int var15 = 2 / Core.TileScale;

            try {
                label442: {
                    Texture var16;
                    float var17;
                    int var19;
                    int var20;
                    label417: {
                        var16 = var1.getCurrentFrameTex();
                        var17 = 0.0F;
                        float var18 = var1.getCurrentFrameTex().getOffsetY();
                        var19 = 0;
                        var20 = 226 - var16.getHeight() * var15;
                        if (var2 == IsoDirections.NW) {
                            break label417;
                        }

                        var19 = 66 - var16.getWidth() * var15;
                    }

                    if (var1.sprite.getProperties().Is(IsoFlagType.WallSE)) {
                        var19 = 6 - var16.getWidth() * var15;
                        var20 = 196 - var16.getHeight() * var15;
                    }

                    if (var1.sprite.name.contains("fencing_01_11")) {
                        var17 = 1.0F;
                    } else if (var1.sprite.name.contains("carpentry_02_80")) {
                        var17 = 1.0F;
                    } else if (var1.sprite.name.contains("spiffos_01_71")) {
                        var17 = -24.0F;
                    } else if (var1.sprite.name.contains("location_community_medical")) {
                        String var29 = var1.sprite.name.replaceAll("(.*)_", "");
                        int var31 = Integer.parseInt(var29);
                        label333:
                        switch (var31) {
                            case 45:
                            case 46:
                            case 47:
                            case 147:
                            case 148:
                            case 149:
                                var17 = -3.0F;
                        }
                    } else {
                        label434: {
                            if (!var1.sprite.name.contains("walls_exterior_roofs")) {
                                break label434;
                            }

                            String var21 = var1.sprite.name.replaceAll("(.*)_", "");
                            int var22 = Integer.parseInt(var21);
                            if (var22 == 4) {
                                var17 = -60.0F;
                            } else if (var22 == 17) {
                                var17 = -46.0F;
                            } else if (var22 == 28 && !var1.sprite.name.contains("03")) {
                                var17 = -60.0F;
                            } else if (var22 == 41) {
                                var17 = -46.0F;
                            }
                        }
                    }

                    label428: {
                        CircleStencilShader var30 = CircleStencilShader.instance;
                        if (var2 != IsoDirections.N && var2 != IsoDirections.NW) {
                            break label428;
                        }

                        short var32 = 700;
                        short var23 = 1084;
                        if (var4) {
                            var23 = 1212;
                            if (!var5) {
                                var32 = 444;
                            }
                        } else if (!var5) {
                            var32 = 828;
                        } else {
                            var32 = 956;
                        }

                        short var24 = 0;
                        if (var6) {
                            var24 = 904;
                            if (!var1.sprite.name.contains("garage") && !var1.sprite.name.contains("industry_trucks")) {
                            }

                            int var25 = var1.sprite.tileSheetIndex;
                            if (var25 % 8 == 5) {
                                var24 = 1356;
                            } else if (var25 % 8 == 4) {
                                var24 = 1582;
                            } else if (var25 % 8 == 3) {
                                var24 = 1130;
                            }
                        } else if (var8) {
                            var24 = 226;
                            if (!var1.sprite.name.contains("trailer")) {
                            }

                            int var37 = var1.sprite.tileSheetIndex;
                            label383:
                            if (var37 != 14 && var37 != 38) {
                                if (var37 != 15 && var37 != 39) {
                                    break label383;
                                }

                                var24 = 452;
                            } else {
                                var24 = 678;
                            }
                        }

                        colu = this.getVertLight(0, var13);
                        coll = this.getVertLight(1, var13);
                        colu2 = this.getVertLight(4, var13);
                        coll2 = this.getVertLight(5, var13);
                        if (Core.bDebug && DebugOptions.instance.DebugDraw_SkipWorldShading.getValue()) {
                            coll2 = -1;
                            colu2 = -1;
                            coll = -1;
                            colu = -1;
                            var14 = defColorInfo;
                        }
                    }

                    if (var2 != IsoDirections.W && var2 != IsoDirections.NW) {
                        break label442;
                    }

                    short var33 = 512;
                    short var34 = 1084;
                    if (var3) {
                        if (!var4) {
                            var33 = 768;
                            var34 = 1212;
                        }
                    } else if (!var4) {
                        var33 = 896;
                        var34 = 1212;
                    } else {
                        var33 = 256;
                    }

                    short var35 = 0;
                    if (var7) {
                        var35 = 904;
                        if (!var1.sprite.name.contains("garage") && !var1.sprite.name.contains("industry_trucks")) {
                        }

                        int var41 = var1.sprite.tileSheetIndex;
                        if (var41 % 8 == 0) {
                            var35 = 1356;
                        } else if (var41 % 8 == 1) {
                            var35 = 1582;
                        } else if (var41 % 8 == 2) {
                            var35 = 1130;
                        }
                    } else {
                        label438: {
                            if (!var9) {
                                break label438;
                            }

                            var35 = 226;
                            if (var1.sprite.name.contains("trailer")) {
                                int var39 = var1.sprite.tileSheetIndex;
                                label349:
                                if (var39 != 13 && var39 != 37) {
                                    if (var39 != 12 && var39 != 36) {
                                        break label349;
                                    }

                                    var35 = 452;
                                } else {
                                    var35 = 678;
                                }
                            }

                            if (var1.sprite.name.contains("sunstarmotel")) {
                                int var40 = var1.sprite.tileSheetIndex;
                                if (var40 == 17) {
                                    var35 = 678;
                                } else if (var40 == 16) {
                                    var35 = 452;
                                }
                            }
                        }
                    }

                    colu = this.getVertLight(0, var13);
                    coll = this.getVertLight(3, var13);
                    colu2 = this.getVertLight(4, var13);
                    coll2 = this.getVertLight(7, var13);
                    if (Core.bDebug && DebugOptions.instance.DebugDraw_SkipWorldShading.getValue()) {
                        coll2 = -1;
                        colu2 = -1;
                        coll = -1;
                        colu = -1;
                        var14 = defColorInfo;
                    }
                }
            } finally {
                SpriteRenderer.instance.setExtraWallShaderParams(null);
                SpriteRenderer.instance.clearCutawayTexture();
                SpriteRenderer.instance.clearUseVertColorsArray();
            }
        }
    }

    public void DoCutawayShaderSprite(IsoSprite var1, IsoDirections var2, boolean var3, boolean var4, boolean var5) {
        CircleStencilShader var6 = CircleStencilShader.instance;
        WallShaperWhole var7 = WallShaperWhole.instance;
        int var8 = IsoCamera.frameState.playerIndex;
        Texture var9 = Texture.getSharedTexture("media/wallcutaways.png");
        if (var9 != null && var9.getID() != -1) {
            int var10 = 2 / Core.TileScale;

            try {
                Texture var11 = ((IsoDirectionFrame)var1.CurrentAnim.Frames.get((int)var1.def.Frame)).getTexture(var2);
                float var12 = 0.0F;
                float var13 = var11.getOffsetY();
                int var14 = 0;
                int var15 = 226 - var11.getHeight() * var10;
                if (var2 == IsoDirections.NW) {
                }

                var14 = 66 - var11.getWidth() * var10;
            } finally {
                SpriteRenderer.instance.setExtraWallShaderParams(null);
                SpriteRenderer.instance.clearCutawayTexture();
                SpriteRenderer.instance.clearUseVertColorsArray();
            }
        }
    }

    public int DoWallLightingNW(
        IsoObject var1, int var2, boolean var3, boolean var4, boolean var5, boolean var6, boolean var7, boolean var8, boolean var9, Shader var10
    ) {
        if (!DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.NW.getValue()) {
            return var2;
        } else {
            boolean var11 = var3 || var4 || var5;
            IsoDirections var12 = IsoDirections.NW;
            int var13 = IsoCamera.frameState.playerIndex;
            colu = this.getVertLight(0, var13);
            coll = this.getVertLight(3, var13);
            colr = this.getVertLight(1, var13);
            colu2 = this.getVertLight(4, var13);
            coll2 = this.getVertLight(7, var13);
            colr2 = this.getVertLight(5, var13);
            if (DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.LightingDebug.getValue()) {
                colu = -65536;
                coll = -16711936;
                colr = -16711681;
                colu2 = -16776961;
                coll2 = -65281;
                colr2 = -256;
            }

            boolean var14 = CircleStencil;
            if (this.z != (int)IsoCamera.CamCharacter.z) {
                var14 = false;
            }

            boolean var15 = var1.sprite.getType() == IsoObjectType.doorFrN || var1.sprite.getType() == IsoObjectType.doorN;
            boolean var16 = var1.sprite.getType() == IsoObjectType.doorFrW || var1.sprite.getType() == IsoObjectType.doorW;
            boolean var17 = false;
            boolean var18 = false;
            boolean var19 = (var15 || var17 || var16 || var17) && var11 || var1.sprite.getProperties().Is(IsoFlagType.NoWallLighting);
            var14 = this.calculateWallAlphaAndCircleStencilCorner(var1, var3, var4, var5, var6, var7, var8, var9, var14, var13, var15, var16, var17, var18);
            if (USE_WALL_SHADER && var14 && var11) {
                this.DoCutawayShader(var1, var12, var3, var4, var5, var6, var7, var8, var9, WallShaperWhole.instance);
                bWallCutawayN = true;
                bWallCutawayW = true;
                return var2;
            } else {
                WallShaperWhole.instance.col[0] = colu2;
                WallShaperWhole.instance.col[1] = colr2;
                WallShaperWhole.instance.col[2] = colr;
                WallShaperWhole.instance.col[3] = colu;
                WallShaperN var20 = WallShaperN.instance;
                var20.col[0] = colu2;
                var20.col[1] = colr2;
                var20.col[2] = colr;
                var20.col[3] = colu;
                var2 = this.performDrawWall(var1, var2, var13, var19, var20, var10);
                WallShaperWhole.instance.col[0] = coll2;
                WallShaperWhole.instance.col[1] = colu2;
                WallShaperWhole.instance.col[2] = colu;
                WallShaperWhole.instance.col[3] = coll;
                WallShaperW var21 = WallShaperW.instance;
                var21.col[0] = coll2;
                var21.col[1] = colu2;
                var21.col[2] = colu;
                var21.col[3] = coll;
                return this.performDrawWall(var1, var2, var13, var19, var21, var10);
            }
        }
    }

    public int DoWallLightingN(IsoObject var1, int var2, boolean var3, boolean var4, boolean var5, boolean var6, Shader var7) {
        if (!DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.N.getValue()) {
            return var2;
        } else {
            boolean var8 = !var5;
            boolean var9 = !var6;
            IsoObjectType var10 = IsoObjectType.doorFrN;
            IsoObjectType var11 = IsoObjectType.doorN;
            boolean var12 = var3 || var4;
            IsoFlagType var13 = IsoFlagType.transparentN;
            IsoFlagType var14 = IsoFlagType.WindowN;
            IsoFlagType var15 = IsoFlagType.HoppableN;
            IsoDirections var16 = IsoDirections.N;
            boolean var17 = CircleStencil;
            int var18 = IsoCamera.frameState.playerIndex;
            colu = this.getVertLight(0, var18);
            coll = this.getVertLight(1, var18);
            colu2 = this.getVertLight(4, var18);
            coll2 = this.getVertLight(5, var18);
            if (DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.LightingDebug.getValue()) {
                colu = -65536;
                coll = -16711936;
                colu2 = -16776961;
                coll2 = -65281;
            }

            WallShaperWhole var19 = WallShaperWhole.instance;
            var19.col[0] = colu2;
            var19.col[1] = coll2;
            var19.col[2] = coll;
            var19.col[3] = colu;
            return this.performDrawWallSegmentSingle(
                var1, var2, false, var3, false, false, var4, var5, var6, var8, var9, var10, var11, var12, var13, var14, var15, var16, var17, var19, var7
            );
        }
    }

    public int DoWallLightingW(IsoObject var1, int var2, boolean var3, boolean var4, boolean var5, boolean var6, Shader var7) {
        if (!DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.W.getValue()) {
            return var2;
        } else {
            boolean var8 = !var5;
            boolean var9 = !var6;
            IsoObjectType var10 = IsoObjectType.doorFrW;
            IsoObjectType var11 = IsoObjectType.doorW;
            boolean var12 = var3 || var4;
            IsoFlagType var13 = IsoFlagType.transparentW;
            IsoFlagType var14 = IsoFlagType.WindowW;
            IsoFlagType var15 = IsoFlagType.HoppableW;
            IsoDirections var16 = IsoDirections.W;
            boolean var17 = CircleStencil;
            int var18 = IsoCamera.frameState.playerIndex;
            colu = this.getVertLight(0, var18);
            coll = this.getVertLight(3, var18);
            colu2 = this.getVertLight(4, var18);
            coll2 = this.getVertLight(7, var18);
            if (DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.LightingDebug.getValue()) {
                colu = -65536;
                coll = -16711936;
                colu2 = -16776961;
                coll2 = -65281;
            }

            WallShaperWhole var19 = WallShaperWhole.instance;
            var19.col[0] = coll2;
            var19.col[1] = colu2;
            var19.col[2] = colu;
            var19.col[3] = coll;
            return this.performDrawWallSegmentSingle(
                var1, var2, var3, var4, var5, var6, false, false, false, var8, var9, var10, var11, var12, var13, var14, var15, var16, var17, var19, var7
            );
        }
    }

    private int performDrawWallSegmentSingle(
        IsoObject var1,
        int var2,
        boolean var3,
        boolean var4,
        boolean var5,
        boolean var6,
        boolean var7,
        boolean var8,
        boolean var9,
        boolean var10,
        boolean var11,
        IsoObjectType var12,
        IsoObjectType var13,
        boolean var14,
        IsoFlagType var15,
        IsoFlagType var16,
        IsoFlagType var17,
        IsoDirections var18,
        boolean var19,
        WallShaperWhole var20,
        Shader var21
    ) {
        int var22 = IsoCamera.frameState.playerIndex;
        if (this.z != (int)IsoCamera.CamCharacter.z) {
            var19 = false;
        }

        boolean var23 = var1.sprite.getType() == var12 || var1.sprite.getType() == var13;
        boolean var24 = var1 instanceof IsoWindow;
        boolean var25 = (var23 || var24) && var14 || var1.sprite.getProperties().Is(IsoFlagType.NoWallLighting);
        var19 = this.calculateWallAlphaAndCircleStencilEdge(var1, var10, var11, var14, var15, var16, var17, var19, var22, var23, var24);
        if (USE_WALL_SHADER && var19 && var14) {
            this.DoCutawayShader(var1, var18, var3, var4, var7, var8, var5, var9, var6, var20);
            bWallCutawayN = bWallCutawayN | var18 == IsoDirections.N;
            bWallCutawayW = bWallCutawayW | var18 == IsoDirections.W;
            return var2;
        } else {
            return this.performDrawWall(var1, var2, var22, var25, var20, var21);
        }
    }

    private int performDrawWallOnly(IsoObject var1, int var2, int var3, boolean var4, Consumer<TextureDraw> var5, Shader var6) {
        if (var2 == 0 && !var4) {
            var2 = this.getCell().getStencilValue(this.x, this.y, this.z);
        }

        IndieGL.enableAlphaTest();
        IndieGL.glAlphaFunc(516, 0.0F);
        IndieGL.glStencilFunc(519, var2, 127);
        if (!var4) {
            IndieGL.glStencilOp(7680, 7680, 7681);
        }

        if (DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.Render.getValue()) {
            var1.renderWallTile((float)this.x, (float)this.y, (float)this.z, var4 ? lightInfoTemp : defColorInfo, true, !var4, var6, var5);
        }

        var1.setAlpha(var3, 1.0F);
        if (var4) {
            IndieGL.glStencilFunc(519, 1, 255);
            IndieGL.glStencilOp(7680, 7680, 7680);
            return var2;
        } else {
            this.getCell().setStencilValue(this.x, this.y, this.z, var2);
            return var2 + 1;
        }
    }

    private int performDrawWall(IsoObject var1, int var2, int var3, boolean var4, Consumer<TextureDraw> var5, Shader var6) {
        lightInfoTemp.set(this.lightInfo[var3]);
        if (Core.bDebug && DebugOptions.instance.DebugDraw_SkipWorldShading.getValue()) {
            var1.render((float)this.x, (float)this.y, (float)this.z, defColorInfo, true, !var4, null);
            return var2;
        } else {
            int var7 = this.performDrawWallOnly(var1, var2, var3, var4, var5, var6);
            if (DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.Walls.AttachedSprites.getValue()) {
                this.renderAttachedSpritesWithNoWallLighting(var1, lightInfoTemp);
            }

            return var7;
        }
    }

    private void calculateWallAlphaCommon(IsoObject var1, boolean var2, boolean var3, boolean var4, int var5, boolean var6, boolean var7) {
        if (var6 || var7) {
            if (var2) {
                var1.setAlpha(var5, 0.4F);
                var1.setTargetAlpha(var5, 0.4F);
                lightInfoTemp.r = Math.max(0.3F, lightInfoTemp.r);
                lightInfoTemp.g = Math.max(0.3F, lightInfoTemp.g);
                lightInfoTemp.b = Math.max(0.3F, lightInfoTemp.b);
                if (var6 && !var3) {
                    var1.setAlpha(var5, 0.0F);
                    var1.setTargetAlpha(var5, 0.0F);
                }

                if (var7 && !var4) {
                    var1.setAlpha(var5, 0.0F);
                    var1.setTargetAlpha(var5, 0.0F);
                }
            }
        }
    }

    private boolean calculateWallAlphaAndCircleStencilEdge(
        IsoObject var1,
        boolean var2,
        boolean var3,
        boolean var4,
        IsoFlagType var5,
        IsoFlagType var6,
        IsoFlagType var7,
        boolean var8,
        int var9,
        boolean var10,
        boolean var11
    ) {
        if (!var10 && !var11) {
        }

        if (!var1.sprite.getProperties().Is("GarageDoor")) {
            var8 = false;
        }

        this.calculateWallAlphaCommon(var1, var4, !var2, !var3, var9, var10, var11);
        return false;
    }

    private boolean calculateWallAlphaAndCircleStencilCorner(
        IsoObject var1,
        boolean var2,
        boolean var3,
        boolean var4,
        boolean var5,
        boolean var6,
        boolean var7,
        boolean var8,
        boolean var9,
        int var10,
        boolean var11,
        boolean var12,
        boolean var13,
        boolean var14
    ) {
        this.calculateWallAlphaCommon(var1, var3 || var4, var5, var7, var10, var11, var13);
        this.calculateWallAlphaCommon(var1, var3 || var2, var6, var8, var10, var12, var14);
        var9 = var9 && !var11 && !var13;
        if (var9
            && var1.sprite.getType() == IsoObjectType.wall
            && (var1.sprite.getProperties().Is(IsoFlagType.transparentN) || var1.sprite.getProperties().Is(IsoFlagType.transparentW))
            && !var1.getSprite().getProperties().Is(IsoFlagType.exterior)
            && !var1.sprite.getProperties().Is(IsoFlagType.WindowN)
            && !var1.sprite.getProperties().Is(IsoFlagType.WindowW)) {
            var9 = false;
        }

        return var9;
    }

    public KahluaTable getLuaMovingObjectList() {
        KahluaTable var1 = LuaManager.platform.newTable();
        LuaManager.env.rawset("Objects", var1);

        for (int var2 = 0; var2 < this.MovingObjects.size(); var2++) {
            var1.rawset(var2 + 1, this.MovingObjects.get(var2));
        }

        return var1;
    }

    public boolean Is(IsoFlagType var1) {
        return this.Properties.Is(var1);
    }

    public boolean Is(String var1) {
        return this.Properties.Is(var1);
    }

    public boolean Has(IsoObjectType var1) {
        if (this.hasTypes.isSet(var1)) {
            return true;
        } else {
            return false;
        }
    }

    public void DeleteTileObject(IsoObject var1) {
        this.Objects.remove(var1);
        this.RecalcAllWithNeighbours(true);
    }

    public KahluaTable getLuaTileObjectList() {
        KahluaTable var1 = LuaManager.platform.newTable();
        LuaManager.env.rawset("Objects", var1);

        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            var1.rawset(var2 + 1, this.Objects.get(var2));
        }

        return var1;
    }

    boolean HasDoor(boolean var1) {
        for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
            if (this.SpecialObjects.get(var2) instanceof IsoDoor && ((IsoDoor)this.SpecialObjects.get(var2)).north == var1) {
                return true;
            }

            if (this.SpecialObjects.get(var2) instanceof IsoThumpable
                && ((IsoThumpable)this.SpecialObjects.get(var2)).isDoor
                && ((IsoThumpable)this.SpecialObjects.get(var2)).north == var1) {
                return true;
            }
        }

        return false;
    }

    public boolean HasStairs() {
        return this.HasStairsNorth() || this.HasStairsWest();
    }

    public boolean HasStairsNorth() {
        return this.Has(IsoObjectType.stairsTN) || this.Has(IsoObjectType.stairsMN) || this.Has(IsoObjectType.stairsBN);
    }

    public boolean HasStairsWest() {
        return this.Has(IsoObjectType.stairsTW) || this.Has(IsoObjectType.stairsMW) || this.Has(IsoObjectType.stairsBW);
    }

    public boolean HasStairsBelow() {
        if (this.z == 0) {
            return false;
        } else {
            IsoGridSquare var1 = this.getCell().getGridSquare(this.x, this.y, this.z - 1);
            return var1 != null && var1.HasStairs();
        }
    }

    public boolean HasElevatedFloor() {
        return this.Has(IsoObjectType.stairsTN) || this.Has(IsoObjectType.stairsMN) || this.Has(IsoObjectType.stairsTW) || this.Has(IsoObjectType.stairsMW);
    }

    public boolean isSameStaircase(int var1, int var2, int var3) {
        if (var3 != this.getZ()) {
            return false;
        } else {
            int var4 = this.getX();
            int var5 = this.getY();
            int var6 = var4;
            int var7 = var5;
            if (this.Has(IsoObjectType.stairsTN)) {
                var7 = var5 + 2;
            } else if (this.Has(IsoObjectType.stairsMN)) {
                var5--;
                var7++;
            } else if (this.Has(IsoObjectType.stairsBN)) {
                var5 -= 2;
            } else if (this.Has(IsoObjectType.stairsTW)) {
                var6 = var4 + 2;
            } else if (this.Has(IsoObjectType.stairsMW)) {
                var4--;
                var6++;
            } else {
                if (!this.Has(IsoObjectType.stairsBW)) {
                    return false;
                }

                var4 -= 2;
            }
        }

        return false;
    }

    public boolean HasSlopedRoof() {
        return this.HasSlopedRoofWest() || this.HasSlopedRoofNorth();
    }

    public boolean HasSlopedRoofWest() {
        return this.Has(IsoObjectType.WestRoofB) || this.Has(IsoObjectType.WestRoofM) || this.Has(IsoObjectType.WestRoofT);
    }

    public boolean HasSlopedRoofNorth() {
        return this.Has(IsoObjectType.WestRoofB) || this.Has(IsoObjectType.WestRoofM) || this.Has(IsoObjectType.WestRoofT);
    }

    public boolean HasTree() {
        return this.hasTree;
    }

    public IsoTree getTree() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoTree var2 = (IsoTree)Type.tryCastTo((IsoObject)this.Objects.get(var1), IsoTree.class);
            if (var2 != null) {
                return var2;
            }
        }

        return null;
    }

    private void fudgeShadowsToAlpha(IsoObject var1, Color var2) {
        float var3 = 1.0F - var1.getAlpha();
        if (var2.r < var3) {
            var2.r = var3;
        }

        if (var2.g < var3) {
            var2.g = var3;
        }

        if (var2.b < var3) {
            var2.b = var3;
        }
    }

    public boolean shouldSave() {
        return !this.Objects.isEmpty();
    }

    public void save(ByteBuffer var1, ObjectOutputStream var2) throws IOException {
        this.save(var1, var2, false);
    }

    public void save(ByteBuffer var1, ObjectOutputStream var2, boolean var3) throws IOException {
        this.getErosionData().save(var1);
        BitHeaderWrite var4 = BitHeader.allocWrite(HeaderSize.Byte, var1);
        int var5 = this.Objects.size();
        if (this.Objects.size() > 0) {
            var4.addFlags(1);
            if (var5 == 2) {
                var4.addFlags(2);
            } else if (var5 == 3) {
                var4.addFlags(4);
            } else if (var5 >= 4) {
                var4.addFlags(8);
            }
        }

        if (this.isOverlayDone()) {
            var4.addFlags(16);
        }

        if (this.haveRoof) {
            var4.addFlags(32);
        }

        BitHeaderWrite var10 = BitHeader.allocWrite(HeaderSize.Byte, var1);
        int var11 = 0;

        for (int var12 = 0; var12 < this.StaticMovingObjects.size(); var12++) {
            if (this.StaticMovingObjects.get(var12) instanceof IsoDeadBody) {
                var11++;
            }
        }

        if (var11 > 0) {
            var10.addFlags(1);
            if (var3) {
                GameWindow.WriteString(var1, "Number of bodies");
            }

            var1.putShort((short)var11);

            for (int var13 = 0; var13 < this.StaticMovingObjects.size(); var13++) {
                IsoMovingObject var14 = this.StaticMovingObjects.get(var13);
                if (var14 instanceof IsoDeadBody) {
                    if (var3) {
                        GameWindow.WriteStringUTF(var1, var14.getClass().getName());
                    }

                    var14.save(var1, var3);
                }
            }
        }

        if (this.table != null && !this.table.isEmpty()) {
            var10.addFlags(2);
            this.table.save(var1);
        }

        if (this.burntOut) {
            var10.addFlags(4);
        }

        if (this.getTrapPositionX() > 0) {
            var10.addFlags(8);
            var1.putInt(this.getTrapPositionX());
            var1.putInt(this.getTrapPositionY());
            var1.putInt(this.getTrapPositionZ());
        }

        if (this.haveSheetRope) {
            var10.addFlags(16);
        }

        if (!var10.equals(0)) {
            var4.addFlags(64);
            var10.write();
        } else {
            var1.position(var10.getStartPosition());
        }
    }

    static void loadmatrix(boolean[][][] var0, DataInputStream var1) throws IOException {
    }

    static void savematrix(boolean[][][] var0, DataOutputStream var1) throws IOException {
        for (int var2 = 0; var2 < 3; var2++) {
            for (int var3 = 0; var3 < 3; var3++) {
                for (int var4 = 0; var4 < 3; var4++) {
                    var1.writeBoolean(var0[var2][var3][var4]);
                }
            }
        }
    }

    public boolean isCommonGrass() {
        if (this.Objects.isEmpty()) {
            return false;
        } else {
            IsoObject var1 = (IsoObject)this.Objects.get(0);
            if (var1.sprite.getProperties().Is(IsoFlagType.solidfloor) && ("TileFloorExt_3".equals(var1.tile) || "TileFloorExt_4".equals(var1.tile))) {
                return true;
            } else {
                return false;
            }
        }
    }

    public static boolean toBoolean(byte[] var0) {
        return var0 != null && var0.length != 0 ? var0[0] != 0 : false;
    }

    public void removeCorpse(IsoDeadBody var1, boolean var2) {
        if (GameClient.bClient && !var2) {
            try {
                GameClient.instance.checkAddedRemovedItems(var1);
            } catch (Exception var4) {
                GameClient.connection.cancelPacket();
                ExceptionLogger.logException(var4);
            }
        }

        var1.removeFromWorld();
        var1.removeFromSquare();
        if (!GameServer.bServer) {
            LuaEventManager.triggerEvent("OnContainerUpdate", this);
        }
    }

    public IsoDeadBody getDeadBody() {
        for (int var1 = 0; var1 < this.StaticMovingObjects.size(); var1++) {
            if (this.StaticMovingObjects.get(var1) instanceof IsoDeadBody) {
                return (IsoDeadBody)this.StaticMovingObjects.get(var1);
            }
        }

        return null;
    }

    public List<IsoDeadBody> getDeadBodys() {
        ArrayList var1 = new ArrayList();

        for (int var2 = 0; var2 < this.StaticMovingObjects.size(); var2++) {
            if (this.StaticMovingObjects.get(var2) instanceof IsoDeadBody) {
                var1.add((IsoDeadBody)this.StaticMovingObjects.get(var2));
            }
        }

        return var1;
    }

    public void addCorpse(IsoDeadBody var1, boolean var2) {
        if (GameClient.bClient && !var2) {
            ByteBufferWriter var3 = GameClient.connection.startPacket();
            PacketType.AddCorpseToMap.doPacket(var3);
            var3.putShort(var1.getObjectID());
            var3.putShort(var1.getOnlineID());
            var3.putInt(this.x);
            var3.putInt(this.y);
            var3.putInt(this.z);
            var1.writeToRemoteBuffer(var3);
            PacketType.AddCorpseToMap.send(GameClient.connection);
        }

        if (!this.StaticMovingObjects.contains(var1)) {
            this.StaticMovingObjects.add(var1);
        }

        var1.addToWorld();
        this.burntOut = false;
        this.Properties.UnSet(IsoFlagType.burntOut);
    }

    public IsoBrokenGlass getBrokenGlass() {
        for (int var1 = 0; var1 < this.SpecialObjects.size(); var1++) {
            IsoObject var2 = this.SpecialObjects.get(var1);
            if (var2 instanceof IsoBrokenGlass) {
                return (IsoBrokenGlass)var2;
            }
        }

        return null;
    }

    public IsoBrokenGlass addBrokenGlass() {
        if (!this.isFree(false)) {
            return this.getBrokenGlass();
        } else {
            IsoBrokenGlass var1 = this.getBrokenGlass();
            if (var1 == null) {
                var1 = new IsoBrokenGlass(this.getCell());
                var1.setSquare(this);
                this.AddSpecialObject(var1);
                if (GameServer.bServer) {
                    GameServer.transmitBrokenGlass(this);
                }
            }

            return var1;
        }
    }

    public void load(ByteBuffer var1, int var2) throws IOException {
        this.load(var1, var2, false);
    }

    public void load(ByteBuffer var1, int var2, boolean var3) throws IOException {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:232
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:310)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 000: aload 0
        // 001: invokevirtual zombie/iso/IsoGridSquare.getErosionData ()Lzombie/erosion/ErosionData$Square;
        // 004: aload 1
        // 005: iload 2
        // 006: invokevirtual zombie/erosion/ErosionData$Square.load (Ljava/nio/ByteBuffer;I)V
        // 009: getstatic zombie/util/io/BitHeader$HeaderSize.Byte Lzombie/util/io/BitHeader$HeaderSize;
        // 00c: aload 1
        // 00d: invokestatic zombie/util/io/BitHeader.allocRead (Lzombie/util/io/BitHeader$HeaderSize;Ljava/nio/ByteBuffer;)Lzombie/util/io/BitHeaderRead;
        // 010: astore 4
        // 012: aload 4
        // 014: bipush 0
        // 015: invokeinterface zombie/util/io/BitHeaderRead.equals (I)Z 2
        // 01a: ifne 48d
        // 01d: aload 4
        // 01f: bipush 1
        // 020: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 025: ifeq 33c
        // 028: iload 3
        // 029: ifeq 037
        // 02c: aload 1
        // 02d: invokestatic zombie/GameWindow.ReadStringUTF (Ljava/nio/ByteBuffer;)Ljava/lang/String;
        // 030: astore 5
        // 032: aload 5
        // 034: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 037: bipush 1
        // 038: istore 5
        // 03a: aload 4
        // 03c: bipush 2
        // 03d: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 042: ifeq 04b
        // 045: bipush 2
        // 046: istore 5
        // 048: goto 06e
        // 04b: aload 4
        // 04d: bipush 4
        // 04e: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 053: ifeq 05c
        // 056: bipush 3
        // 057: istore 5
        // 059: goto 06e
        // 05c: aload 4
        // 05e: bipush 8
        // 060: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 065: ifeq 06e
        // 068: aload 1
        // 069: invokevirtual java/nio/ByteBuffer.getShort ()S
        // 06c: istore 5
        // 06e: bipush 0
        // 06f: istore 6
        // 071: iload 6
        // 073: iload 5
        // 075: if_icmpge 2fe
        // 078: aload 1
        // 079: invokevirtual java/nio/ByteBuffer.position ()I
        // 07c: istore 7
        // 07e: bipush 0
        // 07f: istore 8
        // 081: iload 3
        // 082: ifeq 08b
        // 085: aload 1
        // 086: invokevirtual java/nio/ByteBuffer.getInt ()I
        // 089: istore 8
        // 08b: aload 1
        // 08c: invokevirtual java/nio/ByteBuffer.get ()B
        // 08f: istore 9
        // 091: iload 9
        // 093: bipush 2
        // 094: iand
        // 095: ifeq 09c
        // 098: bipush 1
        // 099: goto 09d
        // 09c: bipush 0
        // 09d: istore 10
        // 09f: iload 9
        // 0a1: bipush 4
        // 0a2: iand
        // 0a3: ifeq 0aa
        // 0a6: bipush 1
        // 0a7: goto 0ab
        // 0aa: bipush 0
        // 0ab: istore 11
        // 0ad: aconst_null
        // 0ae: astore 12
        // 0b0: iload 3
        // 0b1: ifeq 0bf
        // 0b4: aload 1
        // 0b5: invokestatic zombie/GameWindow.ReadStringUTF (Ljava/nio/ByteBuffer;)Ljava/lang/String;
        // 0b8: astore 13
        // 0ba: aload 13
        // 0bc: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 0bf: aload 0
        // 0c0: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 0c3: aload 1
        // 0c4: invokestatic zombie/iso/IsoObject.factoryFromFileInput (Lzombie/iso/IsoCell;Ljava/nio/ByteBuffer;)Lzombie/iso/IsoObject;
        // 0c7: astore 12
        // 0c9: aload 12
        // 0cb: ifnonnull 119
        // 0ce: iload 3
        // 0cf: ifeq 2f8
        // 0d2: aload 1
        // 0d3: invokevirtual java/nio/ByteBuffer.position ()I
        // 0d6: istore 13
        // 0d8: iload 13
        // 0da: iload 7
        // 0dc: isub
        // 0dd: iload 8
        // 0df: if_icmpeq 116
        // 0e2: iload 13
        // 0e4: iload 7
        // 0e6: isub
        // 0e7: iload 8
        // 0e9: iload 5
        // 0eb: invokedynamic makeConcatWithConstants (III)Ljava/lang/String; bsm=java/lang/invoke/StringConcatFactory.makeConcatWithConstants (Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite; args=[ "***** Object loaded size \u0001 != saved size \u0001, reading obj size: \u0001, Object == null" ]
        // 0f0: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 0f3: aload 12
        // 0f5: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 0f8: ifnull 116
        // 0fb: aload 12
        // 0fd: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 100: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 103: ifnull 116
        // 106: aload 12
        // 108: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 10b: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 10e: invokedynamic makeConcatWithConstants (Ljava/lang/String;)Ljava/lang/String; bsm=java/lang/invoke/StringConcatFactory.makeConcatWithConstants (Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite; args=[ "Obj sprite = \u0001" ]
        // 113: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 116: goto 2f8
        // 119: aload 12
        // 11b: aload 0
        // 11c: putfield zombie/iso/IsoObject.square Lzombie/iso/IsoGridSquare;
        // 11f: aload 12
        // 121: aload 1
        // 122: iload 2
        // 123: iload 3
        // 124: invokevirtual zombie/iso/IsoObject.load (Ljava/nio/ByteBuffer;IZ)V
        // 127: goto 146
        // 12a: astore 13
        // 12c: aload 0
        // 12d: invokevirtual zombie/iso/IsoGridSquare.debugPrintGridSquare ()V
        // 130: getstatic zombie/iso/IsoGridSquare.lastLoaded Lzombie/iso/IsoGridSquare;
        // 133: ifnull 13c
        // 136: getstatic zombie/iso/IsoGridSquare.lastLoaded Lzombie/iso/IsoGridSquare;
        // 139: invokevirtual zombie/iso/IsoGridSquare.debugPrintGridSquare ()V
        // 13c: new java/lang/RuntimeException
        // 13f: dup
        // 140: aload 13
        // 142: invokespecial java/lang/RuntimeException.<init> (Ljava/lang/Throwable;)V
        // 145: athrow
        // 146: iload 3
        // 147: ifeq 18e
        // 14a: aload 1
        // 14b: invokevirtual java/nio/ByteBuffer.position ()I
        // 14e: istore 13
        // 150: iload 13
        // 152: iload 7
        // 154: isub
        // 155: iload 8
        // 157: if_icmpeq 18e
        // 15a: iload 13
        // 15c: iload 7
        // 15e: isub
        // 15f: iload 8
        // 161: iload 5
        // 163: invokedynamic makeConcatWithConstants (III)Ljava/lang/String; bsm=java/lang/invoke/StringConcatFactory.makeConcatWithConstants (Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite; args=[ "***** Object loaded size \u0001 != saved size \u0001, reading obj size: \u0001" ]
        // 168: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 16b: aload 12
        // 16d: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 170: ifnull 18e
        // 173: aload 12
        // 175: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 178: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 17b: ifnull 18e
        // 17e: aload 12
        // 180: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 183: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 186: invokedynamic makeConcatWithConstants (Ljava/lang/String;)Ljava/lang/String; bsm=java/lang/invoke/StringConcatFactory.makeConcatWithConstants (Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite; args=[ "Obj sprite = \u0001" ]
        // 18b: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 18e: aload 12
        // 190: instanceof zombie/iso/objects/IsoWorldInventoryObject
        // 193: ifeq 25a
        // 196: aload 12
        // 198: checkcast zombie/iso/objects/IsoWorldInventoryObject
        // 19b: invokevirtual zombie/iso/objects/IsoWorldInventoryObject.getItem ()Lzombie/inventory/InventoryItem;
        // 19e: ifnonnull 1a4
        // 1a1: goto 2f8
        // 1a4: aload 12
        // 1a6: checkcast zombie/iso/objects/IsoWorldInventoryObject
        // 1a9: invokevirtual zombie/iso/objects/IsoWorldInventoryObject.getItem ()Lzombie/inventory/InventoryItem;
        // 1ac: invokevirtual zombie/inventory/InventoryItem.getFullType ()Ljava/lang/String;
        // 1af: astore 13
        // 1b1: getstatic zombie/scripting/ScriptManager.instance Lzombie/scripting/ScriptManager;
        // 1b4: aload 13
        // 1b6: invokevirtual zombie/scripting/ScriptManager.FindItem (Ljava/lang/String;)Lzombie/scripting/objects/Item;
        // 1b9: astore 14
        // 1bb: aload 14
        // 1bd: ifnull 1cb
        // 1c0: aload 14
        // 1c2: invokevirtual zombie/scripting/objects/Item.getObsolete ()Z
        // 1c5: ifeq 1cb
        // 1c8: goto 2f8
        // 1cb: aload 13
        // 1cd: ldc_w "_"
        // 1d0: invokevirtual java/lang/String.split (Ljava/lang/String;)[Ljava/lang/String;
        // 1d3: astore 15
        // 1d5: aload 12
        // 1d7: checkcast zombie/iso/objects/IsoWorldInventoryObject
        // 1da: getfield zombie/iso/objects/IsoWorldInventoryObject.dropTime D
        // 1dd: ldc2_w -1.0
        // 1e0: dcmpl
        // 1e1: ifle 25a
        // 1e4: getstatic zombie/SandboxOptions.instance Lzombie/SandboxOptions;
        // 1e7: getfield zombie/SandboxOptions.HoursForWorldItemRemoval Lzombie/SandboxOptions$DoubleSandboxOption;
        // 1ea: invokevirtual zombie/SandboxOptions$DoubleSandboxOption.getValue ()D
        // 1ed: dconst_0
        // 1ee: dcmpl
        // 1ef: ifle 25a
        // 1f2: getstatic zombie/SandboxOptions.instance Lzombie/SandboxOptions;
        // 1f5: getfield zombie/SandboxOptions.WorldItemRemovalList Lzombie/SandboxOptions$StringSandboxOption;
        // 1f8: invokevirtual zombie/SandboxOptions$StringSandboxOption.getValue ()Ljava/lang/String;
        // 1fb: aload 15
        // 1fd: bipush 0
        // 1fe: aaload
        // 1ff: invokevirtual java/lang/String.contains (Ljava/lang/CharSequence;)Z
        // 202: ifeq 211
        // 205: getstatic zombie/SandboxOptions.instance Lzombie/SandboxOptions;
        // 208: getfield zombie/SandboxOptions.ItemRemovalListBlacklistToggle Lzombie/SandboxOptions$BooleanSandboxOption;
        // 20b: invokevirtual zombie/SandboxOptions$BooleanSandboxOption.getValue ()Z
        // 20e: ifeq 230
        // 211: getstatic zombie/SandboxOptions.instance Lzombie/SandboxOptions;
        // 214: getfield zombie/SandboxOptions.WorldItemRemovalList Lzombie/SandboxOptions$StringSandboxOption;
        // 217: invokevirtual zombie/SandboxOptions$StringSandboxOption.getValue ()Ljava/lang/String;
        // 21a: aload 15
        // 21c: bipush 0
        // 21d: aaload
        // 21e: invokevirtual java/lang/String.contains (Ljava/lang/CharSequence;)Z
        // 221: ifne 25a
        // 224: getstatic zombie/SandboxOptions.instance Lzombie/SandboxOptions;
        // 227: getfield zombie/SandboxOptions.ItemRemovalListBlacklistToggle Lzombie/SandboxOptions$BooleanSandboxOption;
        // 22a: invokevirtual zombie/SandboxOptions$BooleanSandboxOption.getValue ()Z
        // 22d: ifeq 25a
        // 230: aload 12
        // 232: checkcast zombie/iso/objects/IsoWorldInventoryObject
        // 235: invokevirtual zombie/iso/objects/IsoWorldInventoryObject.isIgnoreRemoveSandbox ()Z
        // 238: ifne 25a
        // 23b: getstatic zombie/GameTime.instance Lzombie/GameTime;
        // 23e: invokevirtual zombie/GameTime.getWorldAgeHours ()D
        // 241: aload 12
        // 243: checkcast zombie/iso/objects/IsoWorldInventoryObject
        // 246: getfield zombie/iso/objects/IsoWorldInventoryObject.dropTime D
        // 249: getstatic zombie/SandboxOptions.instance Lzombie/SandboxOptions;
        // 24c: getfield zombie/SandboxOptions.HoursForWorldItemRemoval Lzombie/SandboxOptions$DoubleSandboxOption;
        // 24f: invokevirtual zombie/SandboxOptions$DoubleSandboxOption.getValue ()D
        // 252: dadd
        // 253: dcmpl
        // 254: ifle 25a
        // 257: goto 2f8
        // 25a: aload 12
        // 25c: instanceof zombie/iso/objects/IsoWindow
        // 25f: ifeq 28f
        // 262: aload 12
        // 264: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 267: ifnull 28f
        // 26a: ldc_w "walls_special_01_8"
        // 26d: aload 12
        // 26f: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 272: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 275: invokevirtual java/lang/String.equals (Ljava/lang/Object;)Z
        // 278: ifne 2f8
        // 27b: ldc_w "walls_special_01_9"
        // 27e: aload 12
        // 280: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 283: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 286: invokevirtual java/lang/String.equals (Ljava/lang/Object;)Z
        // 289: ifeq 28f
        // 28c: goto 2f8
        // 28f: aload 0
        // 290: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 293: aload 12
        // 295: invokevirtual zombie/util/list/PZArrayList.add (Ljava/lang/Object;)Z
        // 298: pop
        // 299: iload 10
        // 29b: ifeq 2a8
        // 29e: aload 0
        // 29f: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 2a2: aload 12
        // 2a4: invokevirtual java/util/ArrayList.add (Ljava/lang/Object;)Z
        // 2a7: pop
        // 2a8: iload 11
        // 2aa: ifeq 2f8
        // 2ad: getstatic zombie/core/Core.bDebug Z
        // 2b0: ifeq 2e0
        // 2b3: aload 12
        // 2b5: instanceof zombie/iso/objects/IsoWorldInventoryObject
        // 2b8: ifne 2e0
        // 2bb: iload 9
        // 2bd: aload 12
        // 2bf: invokevirtual zombie/iso/IsoObject.getObjectName ()Ljava/lang/String;
        // 2c2: aload 12
        // 2c4: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 2c7: ifnull 2d5
        // 2ca: aload 12
        // 2cc: invokevirtual zombie/iso/IsoObject.getSprite ()Lzombie/iso/sprite/IsoSprite;
        // 2cf: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 2d2: goto 2d8
        // 2d5: ldc_w "unknown"
        // 2d8: invokedynamic makeConcatWithConstants (BLjava/lang/String;Ljava/lang/String;)Ljava/lang/String; bsm=java/lang/invoke/StringConcatFactory.makeConcatWithConstants (Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite; args=[ "Bitflags = \u0001, obj name = \u0001, sprite = \u0001" ]
        // 2dd: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 2e0: aload 0
        // 2e1: getfield zombie/iso/IsoGridSquare.WorldObjects Ljava/util/ArrayList;
        // 2e4: aload 12
        // 2e6: checkcast zombie/iso/objects/IsoWorldInventoryObject
        // 2e9: invokevirtual java/util/ArrayList.add (Ljava/lang/Object;)Z
        // 2ec: pop
        // 2ed: aload 12
        // 2ef: getfield zombie/iso/IsoObject.square Lzombie/iso/IsoGridSquare;
        // 2f2: getfield zombie/iso/IsoGridSquare.chunk Lzombie/iso/IsoChunk;
        // 2f5: invokevirtual zombie/iso/IsoChunk.recalcHashCodeObjects ()V
        // 2f8: iinc 6 1
        // 2fb: goto 071
        // 2fe: iload 3
        // 2ff: ifeq 33c
        // 302: aload 1
        // 303: invokevirtual java/nio/ByteBuffer.get ()B
        // 306: istore 6
        // 308: aload 1
        // 309: invokevirtual java/nio/ByteBuffer.get ()B
        // 30c: istore 7
        // 30e: aload 1
        // 30f: invokevirtual java/nio/ByteBuffer.get ()B
        // 312: istore 8
        // 314: aload 1
        // 315: invokevirtual java/nio/ByteBuffer.get ()B
        // 318: istore 9
        // 31a: iload 6
        // 31c: bipush 67
        // 31e: if_icmpne 336
        // 321: iload 7
        // 323: bipush 82
        // 325: if_icmpne 336
        // 328: iload 8
        // 32a: bipush 80
        // 32c: if_icmpne 336
        // 32f: iload 9
        // 331: bipush 83
        // 333: if_icmpeq 33c
        // 336: ldc_w "***** Expected CRPS here"
        // 339: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 33c: aload 0
        // 33d: aload 4
        // 33f: bipush 16
        // 341: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 346: invokevirtual zombie/iso/IsoGridSquare.setOverlayDone (Z)V
        // 349: aload 0
        // 34a: aload 4
        // 34c: bipush 32
        // 34e: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 353: putfield zombie/iso/IsoGridSquare.haveRoof Z
        // 356: aload 4
        // 358: bipush 64
        // 35a: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 35f: ifeq 48d
        // 362: getstatic zombie/util/io/BitHeader$HeaderSize.Byte Lzombie/util/io/BitHeader$HeaderSize;
        // 365: aload 1
        // 366: invokestatic zombie/util/io/BitHeader.allocRead (Lzombie/util/io/BitHeader$HeaderSize;Ljava/nio/ByteBuffer;)Lzombie/util/io/BitHeaderRead;
        // 369: astore 5
        // 36b: aload 5
        // 36d: bipush 1
        // 36e: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 373: ifeq 422
        // 376: iload 3
        // 377: ifeq 385
        // 37a: aload 1
        // 37b: invokestatic zombie/GameWindow.ReadStringUTF (Ljava/nio/ByteBuffer;)Ljava/lang/String;
        // 37e: astore 6
        // 380: aload 6
        // 382: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 385: aload 1
        // 386: invokevirtual java/nio/ByteBuffer.getShort ()S
        // 389: istore 6
        // 38b: bipush 0
        // 38c: istore 7
        // 38e: iload 7
        // 390: iload 6
        // 392: if_icmpge 422
        // 395: aconst_null
        // 396: astore 8
        // 398: iload 3
        // 399: ifeq 3a7
        // 39c: aload 1
        // 39d: invokestatic zombie/GameWindow.ReadStringUTF (Ljava/nio/ByteBuffer;)Ljava/lang/String;
        // 3a0: astore 9
        // 3a2: aload 9
        // 3a4: invokestatic zombie/debug/DebugLog.log (Ljava/lang/String;)V
        // 3a7: aload 0
        // 3a8: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 3ab: aload 1
        // 3ac: invokestatic zombie/iso/IsoObject.factoryFromFileInput (Lzombie/iso/IsoCell;Ljava/nio/ByteBuffer;)Lzombie/iso/IsoObject;
        // 3af: checkcast zombie/iso/IsoMovingObject
        // 3b2: astore 8
        // 3b4: goto 3d3
        // 3b7: astore 9
        // 3b9: aload 0
        // 3ba: invokevirtual zombie/iso/IsoGridSquare.debugPrintGridSquare ()V
        // 3bd: getstatic zombie/iso/IsoGridSquare.lastLoaded Lzombie/iso/IsoGridSquare;
        // 3c0: ifnull 3c9
        // 3c3: getstatic zombie/iso/IsoGridSquare.lastLoaded Lzombie/iso/IsoGridSquare;
        // 3c6: invokevirtual zombie/iso/IsoGridSquare.debugPrintGridSquare ()V
        // 3c9: new java/lang/RuntimeException
        // 3cc: dup
        // 3cd: aload 9
        // 3cf: invokespecial java/lang/RuntimeException.<init> (Ljava/lang/Throwable;)V
        // 3d2: athrow
        // 3d3: aload 8
        // 3d5: ifnonnull 3db
        // 3d8: goto 41c
        // 3db: aload 8
        // 3dd: aload 0
        // 3de: putfield zombie/iso/IsoMovingObject.square Lzombie/iso/IsoGridSquare;
        // 3e1: aload 8
        // 3e3: aload 0
        // 3e4: putfield zombie/iso/IsoMovingObject.current Lzombie/iso/IsoGridSquare;
        // 3e7: aload 8
        // 3e9: aload 1
        // 3ea: iload 2
        // 3eb: iload 3
        // 3ec: invokevirtual zombie/iso/IsoMovingObject.load (Ljava/nio/ByteBuffer;IZ)V
        // 3ef: goto 40e
        // 3f2: astore 9
        // 3f4: aload 0
        // 3f5: invokevirtual zombie/iso/IsoGridSquare.debugPrintGridSquare ()V
        // 3f8: getstatic zombie/iso/IsoGridSquare.lastLoaded Lzombie/iso/IsoGridSquare;
        // 3fb: ifnull 404
        // 3fe: getstatic zombie/iso/IsoGridSquare.lastLoaded Lzombie/iso/IsoGridSquare;
        // 401: invokevirtual zombie/iso/IsoGridSquare.debugPrintGridSquare ()V
        // 404: new java/lang/RuntimeException
        // 407: dup
        // 408: aload 9
        // 40a: invokespecial java/lang/RuntimeException.<init> (Ljava/lang/Throwable;)V
        // 40d: athrow
        // 40e: aload 0
        // 40f: getfield zombie/iso/IsoGridSquare.StaticMovingObjects Ljava/util/ArrayList;
        // 412: aload 8
        // 414: invokevirtual java/util/ArrayList.add (Ljava/lang/Object;)Z
        // 417: pop
        // 418: aload 0
        // 419: invokevirtual zombie/iso/IsoGridSquare.recalcHashCodeObjects ()V
        // 41c: iinc 7 1
        // 41f: goto 38e
        // 422: aload 5
        // 424: bipush 2
        // 425: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 42a: ifeq 449
        // 42d: aload 0
        // 42e: getfield zombie/iso/IsoGridSquare.table Lse/krka/kahlua/vm/KahluaTable;
        // 431: ifnonnull 43e
        // 434: aload 0
        // 435: getstatic zombie/Lua/LuaManager.platform Lse/krka/kahlua/j2se/J2SEPlatform;
        // 438: invokevirtual se/krka/kahlua/j2se/J2SEPlatform.newTable ()Lse/krka/kahlua/vm/KahluaTable;
        // 43b: putfield zombie/iso/IsoGridSquare.table Lse/krka/kahlua/vm/KahluaTable;
        // 43e: aload 0
        // 43f: getfield zombie/iso/IsoGridSquare.table Lse/krka/kahlua/vm/KahluaTable;
        // 442: aload 1
        // 443: iload 2
        // 444: invokeinterface se/krka/kahlua/vm/KahluaTable.load (Ljava/nio/ByteBuffer;I)V 3
        // 449: aload 0
        // 44a: aload 5
        // 44c: bipush 4
        // 44d: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 452: putfield zombie/iso/IsoGridSquare.burntOut Z
        // 455: aload 5
        // 457: bipush 8
        // 459: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 45e: ifeq 479
        // 461: aload 0
        // 462: aload 1
        // 463: invokevirtual java/nio/ByteBuffer.getInt ()I
        // 466: invokevirtual zombie/iso/IsoGridSquare.setTrapPositionX (I)V
        // 469: aload 0
        // 46a: aload 1
        // 46b: invokevirtual java/nio/ByteBuffer.getInt ()I
        // 46e: invokevirtual zombie/iso/IsoGridSquare.setTrapPositionY (I)V
        // 471: aload 0
        // 472: aload 1
        // 473: invokevirtual java/nio/ByteBuffer.getInt ()I
        // 476: invokevirtual zombie/iso/IsoGridSquare.setTrapPositionZ (I)V
        // 479: aload 0
        // 47a: aload 5
        // 47c: bipush 16
        // 47e: invokeinterface zombie/util/io/BitHeaderRead.hasFlags (I)Z 2
        // 483: putfield zombie/iso/IsoGridSquare.haveSheetRope Z
        // 486: aload 5
        // 488: invokeinterface zombie/util/io/BitHeaderRead.release ()V 1
        // 48d: aload 4
        // 48f: invokeinterface zombie/util/io/BitHeaderRead.release ()V 1
        // 494: aload 0
        // 495: putstatic zombie/iso/IsoGridSquare.lastLoaded Lzombie/iso/IsoGridSquare;
        // 498: return
    }

    private void debugPrintGridSquare() {
        System.out.println("x=" + this.x + " y=" + this.y + " z=" + this.z);
        System.out.println("objects");

        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            ((IsoObject)this.Objects.get(var1)).debugPrintout();
        }

        System.out.println("staticmovingobjects");

        for (int var2 = 0; var2 < this.StaticMovingObjects.size(); var2++) {
            ((IsoObject)this.Objects.get(var2)).debugPrintout();
        }
    }

    public float scoreAsWaypoint(int var1, int var2) {
        float var3 = 2.0F;
        return var3 - IsoUtils.DistanceManhatten((float)var1, (float)var2, (float)this.getX(), (float)this.getY()) * 5.0F;
    }

    public void InvalidateSpecialObjectPaths() {
    }

    public boolean isSolid() {
        return this.Properties.Is(IsoFlagType.solid);
    }

    public boolean isSolidTrans() {
        return this.Properties.Is(IsoFlagType.solidtrans);
    }

    public boolean isFree(boolean var1) {
        if (var1 && this.MovingObjects.size() > 0) {
            return false;
        } else if (this.CachedIsFree) {
            return this.CacheIsFree;
        } else {
            this.CachedIsFree = true;
            this.CacheIsFree = true;
            if (!this.Properties.Is(IsoFlagType.solid) && !this.Properties.Is(IsoFlagType.solidtrans) && !this.Has(IsoObjectType.tree)) {
            }

            this.CacheIsFree = false;
        }

        return false;
    }

    public boolean isFreeOrMidair(boolean var1) {
        if (var1 && this.MovingObjects.size() > 0) {
            return false;
        } else {
            boolean var2 = true;
            if (!this.Properties.Is(IsoFlagType.solid) && !this.Properties.Is(IsoFlagType.solidtrans) && !this.Has(IsoObjectType.tree)) {
            }

            var2 = false;
        }

        return false;
    }

    public boolean isFreeOrMidair(boolean var1, boolean var2) {
        if (var1 && this.MovingObjects.size() > 0) {
            if (!var2) {
                return false;
            }

            for (int var3 = 0; var3 < this.MovingObjects.size(); var3++) {
                IsoMovingObject var4 = this.MovingObjects.get(var3);
                if (!(var4 instanceof IsoDeadBody)) {
                    return false;
                }
            }
        }

        boolean var5 = true;
        if (!this.Properties.Is(IsoFlagType.solid) && !this.Properties.Is(IsoFlagType.solidtrans) && !this.Has(IsoObjectType.tree)) {
        }

        var5 = false;
        return false;
    }

    public boolean connectedWithFloor() {
        if (this.getZ() == 0) {
            return true;
        } else {
            Object var1 = null;
            var1 = this.getCell().getGridSquare(this.getX() - 1, this.getY(), this.getZ());
            if (var1 != null && ((IsoGridSquare)var1).Properties.Is(IsoFlagType.solidfloor)) {
                return true;
            } else {
                var1 = this.getCell().getGridSquare(this.getX() + 1, this.getY(), this.getZ());
                if (var1 != null && ((IsoGridSquare)var1).Properties.Is(IsoFlagType.solidfloor)) {
                    return true;
                } else {
                    var1 = this.getCell().getGridSquare(this.getX(), this.getY() - 1, this.getZ());
                    if (var1 != null && ((IsoGridSquare)var1).Properties.Is(IsoFlagType.solidfloor)) {
                        return true;
                    } else {
                        var1 = this.getCell().getGridSquare(this.getX(), this.getY() + 1, this.getZ());
                        if (var1 != null && ((IsoGridSquare)var1).Properties.Is(IsoFlagType.solidfloor)) {
                            return true;
                        } else {
                            return false;
                        }
                    }
                }
            }
        }
    }

    public boolean hasFloor(boolean var1) {
        if (this.Properties.Is(IsoFlagType.solidfloor)) {
            return true;
        } else {
            Object var2 = null;
            if (var1) {
                var2 = this.getCell().getGridSquare(this.getX(), this.getY() - 1, this.getZ());
            } else {
                var2 = this.getCell().getGridSquare(this.getX() - 1, this.getY(), this.getZ());
            }
        }

        return false;
    }

    public boolean isNotBlocked(boolean var1) {
        if (!this.CachedIsFree) {
            this.CacheIsFree = true;
            this.CachedIsFree = true;
            if (!this.Properties.Is(IsoFlagType.solid) && !this.Properties.Is(IsoFlagType.solidtrans)) {
            }

            this.CacheIsFree = false;
        } else if (!this.CacheIsFree) {
            return false;
        }

        if (var1 && this.MovingObjects.size() > 0) {
            return false;
        } else {
            return true;
        }
    }

    public IsoObject getDoor(boolean var1) {
        for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
            IsoObject var3 = this.SpecialObjects.get(var2);
            if (var3 instanceof IsoThumpable var4 && var4.isDoor() && var1 == var4.north) {
                return var4;
            }

            if (var3 instanceof IsoDoor var5 && var1 == var5.north) {
                return var5;
            }
        }

        return null;
    }

    public IsoDoor getIsoDoor() {
        for (int var1 = 0; var1 < this.SpecialObjects.size(); var1++) {
            IsoObject var2 = this.SpecialObjects.get(var1);
            if (var2 instanceof IsoDoor) {
                return (IsoDoor)var2;
            }
        }

        return null;
    }

    public IsoObject getDoorTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            IsoObject var2 = null;
            if (var1.x < this.x) {
                var2 = this.getDoor(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y < this.y) {
                var2 = this.getDoor(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x > this.x) {
                var2 = var1.getDoor(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y > this.y) {
                var2 = var1.getDoor(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x != this.x && var1.y != this.y) {
                IsoGridSquare var3 = this.getCell().getGridSquare(this.x, var1.y, this.z);
                IsoGridSquare var4 = this.getCell().getGridSquare(var1.x, this.y, this.z);
                var2 = this.getDoorTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = this.getDoorTo(var4);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getDoorTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getDoorTo(var4);
                if (var2 != null) {
                    return var2;
                }
            }

            return null;
        } else {
            return null;
        }
    }

    public IsoWindow getWindow(boolean var1) {
        for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
            IsoObject var3 = this.SpecialObjects.get(var2);
            if (var3 instanceof IsoWindow var4 && var1 == var4.north) {
                return var4;
            }
        }

        return null;
    }

    public IsoWindow getWindow() {
        for (int var1 = 0; var1 < this.SpecialObjects.size(); var1++) {
            IsoObject var2 = this.SpecialObjects.get(var1);
            if (var2 instanceof IsoWindow) {
                return (IsoWindow)var2;
            }
        }

        return null;
    }

    public IsoWindow getWindowTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            IsoWindow var2 = null;
            if (var1.x < this.x) {
                var2 = this.getWindow(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y < this.y) {
                var2 = this.getWindow(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x > this.x) {
                var2 = var1.getWindow(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y > this.y) {
                var2 = var1.getWindow(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x != this.x && var1.y != this.y) {
                IsoGridSquare var3 = this.getCell().getGridSquare(this.x, var1.y, this.z);
                IsoGridSquare var4 = this.getCell().getGridSquare(var1.x, this.y, this.z);
                var2 = this.getWindowTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = this.getWindowTo(var4);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWindowTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWindowTo(var4);
                if (var2 != null) {
                    return var2;
                }
            }

            return null;
        } else {
            return null;
        }
    }

    public boolean isAdjacentToWindow() {
        if (this.getWindow() != null) {
            return true;
        } else if (this.hasWindowFrame()) {
            return true;
        } else if (this.getThumpableWindow(false) == null && this.getThumpableWindow(true) == null) {
            IsoGridSquare var1 = this.nav[IsoDirections.S.index()];
            if (var1 != null && (var1.getWindow(true) != null || var1.getWindowFrame(true) != null || var1.getThumpableWindow(true) != null)) {
                return true;
            } else {
                IsoGridSquare var2 = this.nav[IsoDirections.E.index()];
                if (var2 != null && (var2.getWindow(false) != null || var2.getWindowFrame(false) != null || var2.getThumpableWindow(false) != null)) {
                    return true;
                } else {
                    return false;
                }
            }
        } else {
            return true;
        }
    }

    public IsoThumpable getThumpableWindow(boolean var1) {
        for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
            IsoObject var3 = this.SpecialObjects.get(var2);
            if (var3 instanceof IsoThumpable var4 && var4.isWindow() && var1 == var4.north) {
                return var4;
            }
        }

        return null;
    }

    public IsoThumpable getWindowThumpableTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            IsoThumpable var2 = null;
            if (var1.x < this.x) {
                var2 = this.getThumpableWindow(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y < this.y) {
                var2 = this.getThumpableWindow(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x > this.x) {
                var2 = var1.getThumpableWindow(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y > this.y) {
                var2 = var1.getThumpableWindow(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x != this.x && var1.y != this.y) {
                IsoGridSquare var3 = this.getCell().getGridSquare(this.x, var1.y, this.z);
                IsoGridSquare var4 = this.getCell().getGridSquare(var1.x, this.y, this.z);
                var2 = this.getWindowThumpableTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = this.getWindowThumpableTo(var4);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWindowThumpableTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWindowThumpableTo(var4);
                if (var2 != null) {
                    return var2;
                }
            }

            return null;
        } else {
            return null;
        }
    }

    public IsoThumpable getHoppableThumpable(boolean var1) {
        for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
            IsoObject var3 = this.SpecialObjects.get(var2);
            if (var3 instanceof IsoThumpable var4 && var4.isHoppable() && var1 == var4.north) {
                return var4;
            }
        }

        return null;
    }

    public IsoThumpable getHoppableThumpableTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            IsoThumpable var2 = null;
            if (var1.x < this.x) {
                var2 = this.getHoppableThumpable(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y < this.y) {
                var2 = this.getHoppableThumpable(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x > this.x) {
                var2 = var1.getHoppableThumpable(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y > this.y) {
                var2 = var1.getHoppableThumpable(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x != this.x && var1.y != this.y) {
                IsoGridSquare var3 = this.getCell().getGridSquare(this.x, var1.y, this.z);
                IsoGridSquare var4 = this.getCell().getGridSquare(var1.x, this.y, this.z);
                var2 = this.getHoppableThumpableTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = this.getHoppableThumpableTo(var4);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getHoppableThumpableTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getHoppableThumpableTo(var4);
                if (var2 != null) {
                    return var2;
                }
            }

            return null;
        } else {
            return null;
        }
    }

    public IsoObject getWallHoppable(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            if (((IsoObject)this.Objects.get(var2)).isHoppable() && var1 == ((IsoObject)this.Objects.get(var2)).isNorthHoppable()) {
                return (IsoObject)this.Objects.get(var2);
            }
        }

        return null;
    }

    public IsoObject getWallHoppableTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            IsoObject var2 = null;
            if (var1.x < this.x) {
                var2 = this.getWallHoppable(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y < this.y) {
                var2 = this.getWallHoppable(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x > this.x) {
                var2 = var1.getWallHoppable(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y > this.y) {
                var2 = var1.getWallHoppable(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x != this.x && var1.y != this.y) {
                IsoGridSquare var3 = this.getCell().getGridSquare(this.x, var1.y, this.z);
                IsoGridSquare var4 = this.getCell().getGridSquare(var1.x, this.y, this.z);
                var2 = this.getWallHoppableTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = this.getWallHoppableTo(var4);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWallHoppableTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWallHoppableTo(var4);
                if (var2 != null) {
                    return var2;
                }
            }

            return null;
        } else {
            return null;
        }
    }

    public IsoObject getBedTo(IsoGridSquare var1) {
        Object var2 = null;
        if (var1.y >= this.y && var1.x >= this.x) {
            var2 = var1.SpecialObjects;
        } else {
            var2 = this.SpecialObjects;
        }

        return null;
    }

    public IsoObject getWindowFrame(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (!(var3 instanceof IsoWorldInventoryObject) && IsoWindowFrame.isWindowFrame(var3, var1)) {
                return var3;
            }
        }

        return null;
    }

    public IsoObject getWindowFrameTo(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            IsoObject var2 = null;
            if (var1.x < this.x) {
                var2 = this.getWindowFrame(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y < this.y) {
                var2 = this.getWindowFrame(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x > this.x) {
                var2 = var1.getWindowFrame(false);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.y > this.y) {
                var2 = var1.getWindowFrame(true);
                if (var2 != null) {
                    return var2;
                }
            }

            if (var1.x != this.x && var1.y != this.y) {
                IsoGridSquare var3 = this.getCell().getGridSquare(this.x, var1.y, this.z);
                IsoGridSquare var4 = this.getCell().getGridSquare(var1.x, this.y, this.z);
                var2 = this.getWindowFrameTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = this.getWindowFrameTo(var4);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWindowFrameTo(var3);
                if (var2 != null) {
                    return var2;
                }

                var2 = var1.getWindowFrameTo(var4);
                if (var2 != null) {
                    return var2;
                }
            }

            return null;
        } else {
            return null;
        }
    }

    public boolean hasWindowFrame() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (!(var2 instanceof IsoWorldInventoryObject) && IsoWindowFrame.isWindowFrame(var2)) {
                return true;
            }
        }

        return false;
    }

    public boolean hasWindowOrWindowFrame() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (!(var2 instanceof IsoWorldInventoryObject) && (this.isWindowOrWindowFrame(var2, true) || this.isWindowOrWindowFrame(var2, false))) {
                return true;
            }
        }

        return false;
    }

    private IsoObject getSpecialWall(boolean var1) {
        for (int var2 = this.SpecialObjects.size() - 1; var2 >= 0; var2--) {
            IsoObject var3 = this.SpecialObjects.get(var2);
            if (var3 instanceof IsoThumpable var4) {
                if (var4.isStairs() || !var4.isThumpable() && !var4.isWindow() && !var4.isDoor() || var4.isDoor() && var4.open || var4.isBlockAllTheSquare()) {
                    continue;
                }

                if (var1 == var4.north && !var4.isCorner()) {
                    return var4;
                }
            }

            if (var3 instanceof IsoWindow var6 && var1 == var6.north) {
                return var6;
            }

            if (var3 instanceof IsoDoor var7 && var1 == var7.north && !var7.open) {
                return var7;
            }
        }

        if (var1 && !this.Is(IsoFlagType.WindowN) || !var1 && !this.Is(IsoFlagType.WindowW)) {
            return null;
        } else {
            IsoObject var5 = this.getWindowFrame(var1);
            if (var5 != null) {
                return var5;
            } else {
                return null;
            }
        }
    }

    public IsoObject getSheetRope() {
        for (int var1 = 0; var1 < this.getObjects().size(); var1++) {
            IsoObject var2 = (IsoObject)this.getObjects().get(var1);
            if (var2.sheetRope) {
                return var2;
            }
        }

        return null;
    }

    public boolean damageSpriteSheetRopeFromBottom(IsoPlayer var1, boolean var2) {
        IsoGridSquare var4 = this;
        IsoFlagType var3;
        if (var2) {
            if (this.Is(IsoFlagType.climbSheetN)) {
                var3 = IsoFlagType.climbSheetN;
            } else {
                if (!this.Is(IsoFlagType.climbSheetS)) {
                    return false;
                }

                var3 = IsoFlagType.climbSheetS;
            }
        } else if (this.Is(IsoFlagType.climbSheetW)) {
            var3 = IsoFlagType.climbSheetW;
        } else {
            if (!this.Is(IsoFlagType.climbSheetE)) {
                return false;
            }

            var3 = IsoFlagType.climbSheetE;
        }

        return false;
    }

    public boolean removeSheetRopeFromBottom(IsoPlayer var1, boolean var2) {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:123
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:310)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 000: aload 0
        // 001: astore 6
        // 003: iload 2
        // 004: ifeq 08d
        // 007: aload 0
        // 008: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetN Lzombie/iso/SpriteDetails/IsoFlagType;
        // 00b: invokevirtual zombie/iso/IsoGridSquare.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 00e: ifeq 01d
        // 011: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetTopN Lzombie/iso/SpriteDetails/IsoFlagType;
        // 014: astore 3
        // 015: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetN Lzombie/iso/SpriteDetails/IsoFlagType;
        // 018: astore 4
        // 01a: goto 113
        // 01d: aload 0
        // 01e: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetS Lzombie/iso/SpriteDetails/IsoFlagType;
        // 021: invokevirtual zombie/iso/IsoGridSquare.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 024: ifeq 08b
        // 027: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetTopS Lzombie/iso/SpriteDetails/IsoFlagType;
        // 02a: astore 3
        // 02b: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetS Lzombie/iso/SpriteDetails/IsoFlagType;
        // 02e: astore 4
        // 030: ldc_w "crafted_01_4"
        // 033: astore 5
        // 035: bipush 0
        // 036: istore 7
        // 038: iload 7
        // 03a: aload 6
        // 03c: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 03f: invokevirtual zombie/util/list/PZArrayList.size ()I
        // 042: if_icmpge 088
        // 045: aload 6
        // 047: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 04a: iload 7
        // 04c: invokevirtual zombie/util/list/PZArrayList.get (I)Ljava/lang/Object;
        // 04f: checkcast zombie/iso/IsoObject
        // 052: astore 8
        // 054: aload 8
        // 056: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 059: ifnull 082
        // 05c: aload 8
        // 05e: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 061: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 064: ifnull 082
        // 067: aload 8
        // 069: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 06c: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 06f: aload 5
        // 071: invokevirtual java/lang/String.equals (Ljava/lang/Object;)Z
        // 074: ifeq 082
        // 077: aload 6
        // 079: aload 8
        // 07b: invokevirtual zombie/iso/IsoGridSquare.transmitRemoveItemFromSquare (Lzombie/iso/IsoObject;)I
        // 07e: pop
        // 07f: goto 088
        // 082: iinc 7 1
        // 085: goto 038
        // 088: goto 113
        // 08b: bipush 0
        // 08c: ireturn
        // 08d: aload 0
        // 08e: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetW Lzombie/iso/SpriteDetails/IsoFlagType;
        // 091: invokevirtual zombie/iso/IsoGridSquare.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 094: ifeq 0a3
        // 097: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetTopW Lzombie/iso/SpriteDetails/IsoFlagType;
        // 09a: astore 3
        // 09b: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetW Lzombie/iso/SpriteDetails/IsoFlagType;
        // 09e: astore 4
        // 0a0: goto 113
        // 0a3: aload 0
        // 0a4: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetE Lzombie/iso/SpriteDetails/IsoFlagType;
        // 0a7: invokevirtual zombie/iso/IsoGridSquare.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 0aa: ifeq 111
        // 0ad: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetTopE Lzombie/iso/SpriteDetails/IsoFlagType;
        // 0b0: astore 3
        // 0b1: getstatic zombie/iso/SpriteDetails/IsoFlagType.climbSheetE Lzombie/iso/SpriteDetails/IsoFlagType;
        // 0b4: astore 4
        // 0b6: ldc_w "crafted_01_3"
        // 0b9: astore 5
        // 0bb: bipush 0
        // 0bc: istore 7
        // 0be: iload 7
        // 0c0: aload 6
        // 0c2: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 0c5: invokevirtual zombie/util/list/PZArrayList.size ()I
        // 0c8: if_icmpge 10e
        // 0cb: aload 6
        // 0cd: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 0d0: iload 7
        // 0d2: invokevirtual zombie/util/list/PZArrayList.get (I)Ljava/lang/Object;
        // 0d5: checkcast zombie/iso/IsoObject
        // 0d8: astore 8
        // 0da: aload 8
        // 0dc: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 0df: ifnull 108
        // 0e2: aload 8
        // 0e4: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 0e7: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 0ea: ifnull 108
        // 0ed: aload 8
        // 0ef: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 0f2: invokevirtual zombie/iso/sprite/IsoSprite.getName ()Ljava/lang/String;
        // 0f5: aload 5
        // 0f7: invokevirtual java/lang/String.equals (Ljava/lang/Object;)Z
        // 0fa: ifeq 108
        // 0fd: aload 6
        // 0ff: aload 8
        // 101: invokevirtual zombie/iso/IsoGridSquare.transmitRemoveItemFromSquare (Lzombie/iso/IsoObject;)I
        // 104: pop
        // 105: goto 10e
        // 108: iinc 7 1
        // 10b: goto 0be
        // 10e: goto 113
        // 111: bipush 0
        // 112: ireturn
        // 113: bipush 0
        // 114: istore 7
        // 116: aconst_null
        // 117: astore 8
        // 119: aload 6
        // 11b: ifnull 1db
        // 11e: bipush 0
        // 11f: istore 9
        // 121: iload 9
        // 123: aload 6
        // 125: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 128: invokevirtual zombie/util/list/PZArrayList.size ()I
        // 12b: if_icmpge 1ad
        // 12e: aload 6
        // 130: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 133: iload 9
        // 135: invokevirtual zombie/util/list/PZArrayList.get (I)Ljava/lang/Object;
        // 138: checkcast zombie/iso/IsoObject
        // 13b: astore 10
        // 13d: aload 10
        // 13f: invokevirtual zombie/iso/IsoObject.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 142: ifnull 1a7
        // 145: aload 10
        // 147: invokevirtual zombie/iso/IsoObject.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 14a: aload 3
        // 14b: invokevirtual zombie/core/properties/PropertyContainer.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 14e: ifne 15e
        // 151: aload 10
        // 153: invokevirtual zombie/iso/IsoObject.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 156: aload 4
        // 158: invokevirtual zombie/core/properties/PropertyContainer.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 15b: ifeq 1a7
        // 15e: aload 6
        // 160: astore 8
        // 162: bipush 1
        // 163: istore 7
        // 165: aload 6
        // 167: aload 10
        // 169: invokevirtual zombie/iso/IsoGridSquare.transmitRemoveItemFromSquare (Lzombie/iso/IsoObject;)I
        // 16c: pop
        // 16d: getstatic zombie/network/GameServer.bServer Z
        // 170: ifeq 193
        // 173: aload 1
        // 174: ifnull 1ad
        // 177: aload 1
        // 178: ldc_w "addItemOfType"
        // 17b: bipush 2
        // 17c: anewarray 639
        // 17f: dup
        // 180: bipush 0
        // 181: ldc_w "type"
        // 184: aastore
        // 185: dup
        // 186: bipush 1
        // 187: aload 10
        // 189: invokevirtual zombie/iso/IsoObject.getName ()Ljava/lang/String;
        // 18c: aastore
        // 18d: invokevirtual zombie/characters/IsoPlayer.sendObjectChange (Ljava/lang/String;[Ljava/lang/Object;)V
        // 190: goto 1ad
        // 193: aload 1
        // 194: ifnull 1ad
        // 197: aload 1
        // 198: invokevirtual zombie/characters/IsoPlayer.getInventory ()Lzombie/inventory/ItemContainer;
        // 19b: aload 10
        // 19d: invokevirtual zombie/iso/IsoObject.getName ()Ljava/lang/String;
        // 1a0: invokevirtual zombie/inventory/ItemContainer.AddItem (Ljava/lang/String;)Lzombie/inventory/InventoryItem;
        // 1a3: pop
        // 1a4: goto 1ad
        // 1a7: iinc 9 1
        // 1aa: goto 121
        // 1ad: aload 6
        // 1af: invokevirtual zombie/iso/IsoGridSquare.getZ ()I
        // 1b2: bipush 7
        // 1b4: if_icmpne 1ba
        // 1b7: goto 1db
        // 1ba: aload 6
        // 1bc: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 1bf: aload 6
        // 1c1: invokevirtual zombie/iso/IsoGridSquare.getX ()I
        // 1c4: aload 6
        // 1c6: invokevirtual zombie/iso/IsoGridSquare.getY ()I
        // 1c9: aload 6
        // 1cb: invokevirtual zombie/iso/IsoGridSquare.getZ ()I
        // 1ce: bipush 1
        // 1cf: iadd
        // 1d0: invokevirtual zombie/iso/IsoCell.getGridSquare (III)Lzombie/iso/IsoGridSquare;
        // 1d3: astore 6
        // 1d5: bipush 0
        // 1d6: istore 7
        // 1d8: goto 119
        // 1db: iload 7
        // 1dd: ifne 272
        // 1e0: aload 8
        // 1e2: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 1e5: aload 8
        // 1e7: invokevirtual zombie/iso/IsoGridSquare.getX ()I
        // 1ea: aload 8
        // 1ec: invokevirtual zombie/iso/IsoGridSquare.getY ()I
        // 1ef: aload 8
        // 1f1: invokevirtual zombie/iso/IsoGridSquare.getZ ()I
        // 1f4: invokevirtual zombie/iso/IsoCell.getGridSquare (III)Lzombie/iso/IsoGridSquare;
        // 1f7: astore 6
        // 1f9: iload 2
        // 1fa: ifeq 20c
        // 1fd: aload 6
        // 1ff: getfield zombie/iso/IsoGridSquare.nav [Lzombie/iso/IsoGridSquare;
        // 202: getstatic zombie/iso/IsoDirections.S Lzombie/iso/IsoDirections;
        // 205: invokevirtual zombie/iso/IsoDirections.index ()I
        // 208: aaload
        // 209: goto 218
        // 20c: aload 6
        // 20e: getfield zombie/iso/IsoGridSquare.nav [Lzombie/iso/IsoGridSquare;
        // 211: getstatic zombie/iso/IsoDirections.E Lzombie/iso/IsoDirections;
        // 214: invokevirtual zombie/iso/IsoDirections.index ()I
        // 217: aaload
        // 218: astore 9
        // 21a: aload 9
        // 21c: ifnonnull 221
        // 21f: bipush 1
        // 220: ireturn
        // 221: bipush 0
        // 222: istore 10
        // 224: iload 10
        // 226: aload 9
        // 228: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 22b: invokevirtual zombie/util/list/PZArrayList.size ()I
        // 22e: if_icmpge 272
        // 231: aload 9
        // 233: invokevirtual zombie/iso/IsoGridSquare.getObjects ()Lzombie/util/list/PZArrayList;
        // 236: iload 10
        // 238: invokevirtual zombie/util/list/PZArrayList.get (I)Ljava/lang/Object;
        // 23b: checkcast zombie/iso/IsoObject
        // 23e: astore 11
        // 240: aload 11
        // 242: invokevirtual zombie/iso/IsoObject.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 245: ifnull 26c
        // 248: aload 11
        // 24a: invokevirtual zombie/iso/IsoObject.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 24d: aload 3
        // 24e: invokevirtual zombie/core/properties/PropertyContainer.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 251: ifne 261
        // 254: aload 11
        // 256: invokevirtual zombie/iso/IsoObject.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 259: aload 4
        // 25b: invokevirtual zombie/core/properties/PropertyContainer.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 25e: ifeq 26c
        // 261: aload 9
        // 263: aload 11
        // 265: invokevirtual zombie/iso/IsoGridSquare.transmitRemoveItemFromSquare (Lzombie/iso/IsoObject;)I
        // 268: pop
        // 269: goto 272
        // 26c: iinc 10 1
        // 26f: goto 224
        // 272: bipush 1
        // 273: ireturn
        return false;
    }

    private IsoObject getSpecialSolid() {
        for (int var1 = 0; var1 < this.SpecialObjects.size(); var1++) {
            IsoObject var2 = this.SpecialObjects.get(var1);
            if (var2 instanceof IsoThumpable var3 && !var3.isStairs() && var3.isThumpable() && var3.isBlockAllTheSquare()) {
                if (var3.getProperties().Is(IsoFlagType.solidtrans) && this.isAdjacentToWindow()) {
                    return null;
                }

                return var3;
            }
        }

        for (int var4 = 0; var4 < this.Objects.size(); var4++) {
            IsoObject var5 = (IsoObject)this.Objects.get(var4);
            if (var5.isMovedThumpable()) {
                if (this.isAdjacentToWindow()) {
                    return null;
                }

                return var5;
            }
        }

        return null;
    }

    public IsoObject testCollideSpecialObjects(IsoGridSquare var1) {
        if (var1 != null && var1 != this) {
            if (var1.x < this.x && var1.y == this.y) {
                if (var1.z == this.z && this.Has(IsoObjectType.stairsTW)) {
                    return null;
                } else {
                    IsoObject var37 = this.getSpecialWall(false);
                    if (var37 != null) {
                        return var37;
                    } else if (this.isBlockedTo(var1)) {
                        return null;
                    } else {
                        var37 = var1.getSpecialSolid();
                        if (var37 != null) {
                            return var37;
                        } else {
                            return null;
                        }
                    }
                }
            } else if (var1.x == this.x && var1.y < this.y) {
                if (var1.z == this.z && this.Has(IsoObjectType.stairsTN)) {
                    return null;
                } else {
                    IsoObject var35 = this.getSpecialWall(true);
                    if (var35 != null) {
                        return var35;
                    } else if (this.isBlockedTo(var1)) {
                        return null;
                    } else {
                        var35 = var1.getSpecialSolid();
                        if (var35 != null) {
                            return var35;
                        } else {
                            return null;
                        }
                    }
                }
            } else if (var1.x > this.x && var1.y == this.y) {
                IsoObject var33 = var1.getSpecialWall(false);
                if (var33 != null) {
                    return var33;
                } else if (this.isBlockedTo(var1)) {
                    return null;
                } else {
                    var33 = var1.getSpecialSolid();
                    if (var33 != null) {
                        return var33;
                    } else {
                        return null;
                    }
                }
            } else if (var1.x == this.x && var1.y > this.y) {
                IsoObject var31 = var1.getSpecialWall(true);
                if (var31 != null) {
                    return var31;
                } else if (this.isBlockedTo(var1)) {
                    return null;
                } else {
                    var31 = var1.getSpecialSolid();
                    if (var31 != null) {
                        return var31;
                    } else {
                        return null;
                    }
                }
            } else if (var1.x < this.x && var1.y < this.y) {
                IsoObject var24 = this.getSpecialWall(true);
                if (var24 != null) {
                    return var24;
                } else {
                    var24 = this.getSpecialWall(false);
                    if (var24 != null) {
                        return var24;
                    } else {
                        IsoGridSquare var41 = this.getCell().getGridSquare(this.x, this.y - 1, this.z);
                        if (var41 != null && !this.isBlockedTo(var41)) {
                            var24 = var41.getSpecialSolid();
                            if (var24 != null) {
                                return var24;
                            }

                            var24 = var41.getSpecialWall(false);
                            if (var24 != null) {
                                return var24;
                            }
                        }

                        IsoGridSquare var44 = this.getCell().getGridSquare(this.x - 1, this.y, this.z);
                        if (var44 != null && !this.isBlockedTo(var44)) {
                            var24 = var44.getSpecialSolid();
                            if (var24 != null) {
                                return var24;
                            }

                            var24 = var44.getSpecialWall(true);
                            if (var24 != null) {
                                return var24;
                            }
                        }

                        if (var41 != null && !this.isBlockedTo(var41) && var44 != null && !this.isBlockedTo(var44)) {
                            if (!var41.isBlockedTo(var1) && !var44.isBlockedTo(var1)) {
                                var24 = var1.getSpecialSolid();
                                if (var24 != null) {
                                    return var24;
                                } else {
                                    return null;
                                }
                            } else {
                                return null;
                            }
                        } else {
                            return null;
                        }
                    }
                }
            } else if (var1.x > this.x && var1.y < this.y) {
                IsoObject var17 = this.getSpecialWall(true);
                if (var17 != null) {
                    return var17;
                } else {
                    IsoGridSquare var40 = this.getCell().getGridSquare(this.x, this.y - 1, this.z);
                    if (var40 != null && !this.isBlockedTo(var40)) {
                        var17 = var40.getSpecialSolid();
                        if (var17 != null) {
                            return var17;
                        }
                    }

                    IsoGridSquare var43 = this.getCell().getGridSquare(this.x + 1, this.y, this.z);
                    if (var43 != null) {
                        var17 = var43.getSpecialWall(false);
                        if (var17 != null) {
                            return var17;
                        }

                        if (!this.isBlockedTo(var43)) {
                            var17 = var43.getSpecialSolid();
                            if (var17 != null) {
                                return var17;
                            }

                            var17 = var43.getSpecialWall(true);
                            if (var17 != null) {
                                return var17;
                            }
                        }
                    }

                    if (var40 != null && !this.isBlockedTo(var40) && var43 != null && !this.isBlockedTo(var43)) {
                        var17 = var1.getSpecialWall(false);
                        if (var17 != null) {
                            return var17;
                        } else if (!var40.isBlockedTo(var1) && !var43.isBlockedTo(var1)) {
                            var17 = var1.getSpecialSolid();
                            if (var17 != null) {
                                return var17;
                            } else {
                                return null;
                            }
                        } else {
                            return null;
                        }
                    } else {
                        return null;
                    }
                }
            } else if (var1.x > this.x && var1.y > this.y) {
                IsoGridSquare var39 = this.getCell().getGridSquare(this.x, this.y + 1, this.z);
                if (var39 != null) {
                    IsoObject var10 = var39.getSpecialWall(true);
                    if (var10 != null) {
                        return var10;
                    }

                    if (!this.isBlockedTo(var39)) {
                        var10 = var39.getSpecialSolid();
                        if (var10 != null) {
                            return var10;
                        }
                    }
                }

                IsoGridSquare var42 = this.getCell().getGridSquare(this.x + 1, this.y, this.z);
                if (var42 != null) {
                    IsoObject var12 = var42.getSpecialWall(false);
                    if (var12 != null) {
                        return var12;
                    }

                    if (!this.isBlockedTo(var42)) {
                        var12 = var42.getSpecialSolid();
                        if (var12 != null) {
                            return var12;
                        }
                    }
                }

                if (var39 != null && !this.isBlockedTo(var39) && var42 != null && !this.isBlockedTo(var42)) {
                    IsoObject var14 = var1.getSpecialWall(false);
                    if (var14 != null) {
                        return var14;
                    } else {
                        var14 = var1.getSpecialWall(true);
                        if (var14 != null) {
                            return var14;
                        } else if (!var39.isBlockedTo(var1) && !var42.isBlockedTo(var1)) {
                            var14 = var1.getSpecialSolid();
                            if (var14 != null) {
                                return var14;
                            } else {
                                return null;
                            }
                        } else {
                            return null;
                        }
                    }
                } else {
                    return null;
                }
            } else if (var1.x < this.x && var1.y > this.y) {
                IsoObject var2 = this.getSpecialWall(false);
                if (var2 != null) {
                    return var2;
                } else {
                    IsoGridSquare var3 = this.getCell().getGridSquare(this.x, this.y + 1, this.z);
                    if (var3 != null) {
                        var2 = var3.getSpecialWall(true);
                        if (var2 != null) {
                            return var2;
                        }

                        if (!this.isBlockedTo(var3)) {
                            var2 = var3.getSpecialSolid();
                            if (var2 != null) {
                                return var2;
                            }
                        }
                    }

                    IsoGridSquare var4 = this.getCell().getGridSquare(this.x - 1, this.y, this.z);
                    if (var4 != null && !this.isBlockedTo(var4)) {
                        var2 = var4.getSpecialSolid();
                        if (var2 != null) {
                            return var2;
                        }
                    }

                    if (var3 != null && !this.isBlockedTo(var3) && var4 != null && !this.isBlockedTo(var4)) {
                        var2 = var1.getSpecialWall(true);
                        if (var2 != null) {
                            return var2;
                        } else if (!var3.isBlockedTo(var1) && !var4.isBlockedTo(var1)) {
                            var2 = var1.getSpecialSolid();
                            if (var2 != null) {
                                return var2;
                            } else {
                                return null;
                            }
                        } else {
                            return null;
                        }
                    } else {
                        return null;
                    }
                }
            } else {
                return null;
            }
        } else {
            return null;
        }
    }

    public IsoObject getDoorFrameTo(IsoGridSquare var1) {
        Object var2 = null;
        if (var1.y >= this.y && var1.x >= this.x) {
            var2 = var1.SpecialObjects;
        } else {
            var2 = this.SpecialObjects;
        }

        return null;
    }

    public static void getSquaresForThread(ArrayDeque<IsoGridSquare> var0, int var1) {
        for (int var2 = 0; var2 < var1; var2++) {
            IsoGridSquare var3 = isoGridSquareCache.poll();
            if (var3 == null) {
                var0.add(new IsoGridSquare(null, null, 0, 0, 0));
            } else {
                var0.add(var3);
            }
        }
    }

    public static IsoGridSquare getNew(IsoCell var0, SliceY var1, int var2, int var3, int var4) {
        IsoGridSquare var5 = isoGridSquareCache.poll();
        if (var5 == null) {
            return new IsoGridSquare(var0, var1, var2, var3, var4);
        } else {
            var5.x = var2;
            var5.y = var3;
            var5.z = var4;
            var5.CachedScreenValue = -1;
            col = 0;
            path = 0;
            pathdoor = 0;
            vision = 0;
            var5.collideMatrix = 134217727;
            var5.pathMatrix = 134217727;
            var5.visionMatrix = 0;
            return var5;
        }
    }

    public static IsoGridSquare getNew(ArrayDeque<IsoGridSquare> var0, IsoCell var1, SliceY var2, int var3, int var4, int var5) {
        IsoGridSquare var6 = null;
        if (var0.isEmpty()) {
            return new IsoGridSquare(var1, var2, var3, var4, var5);
        } else {
            var6 = (IsoGridSquare)var0.pop();
            var6.x = var3;
            var6.y = var4;
            var6.z = var5;
            var6.CachedScreenValue = -1;
            col = 0;
            path = 0;
            pathdoor = 0;
            vision = 0;
            var6.collideMatrix = 134217727;
            var6.pathMatrix = 134217727;
            var6.visionMatrix = 0;
            return var6;
        }
    }

    @Deprecated
    public long getHashCodeObjects() {
        this.recalcHashCodeObjects();
        return this.hashCodeObjects;
    }

    @Deprecated
    public int getHashCodeObjectsInt() {
        this.recalcHashCodeObjects();
        return (int)this.hashCodeObjects;
    }

    @Deprecated
    public void recalcHashCodeObjects() {
        long var1 = 0L;
        this.hashCodeObjects = var1;
    }

    @Deprecated
    public int hashCodeNoOverride() {
        int var1 = 0;
        this.recalcHashCodeObjects();
        var1 = var1 * 2 + this.Objects.size();
        var1 = (int)((long)var1 + this.getHashCodeObjects());

        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            var1 = var1 * 2 + ((IsoObject)this.Objects.get(var2)).hashCode();
        }

        int var13 = 0;

        for (int var3 = 0; var3 < this.StaticMovingObjects.size(); var3++) {
            if (this.StaticMovingObjects.get(var3) instanceof IsoDeadBody) {
                var13++;
            }
        }

        var1 = var1 * 2 + var13;

        for (int var14 = 0; var14 < this.StaticMovingObjects.size(); var14++) {
            IsoMovingObject var4 = this.StaticMovingObjects.get(var14);
            if (var4 instanceof IsoDeadBody) {
                var1 = var1 * 2 + var4.hashCode();
            }
        }

        if (this.table != null && !this.table.isEmpty()) {
            var1 = var1 * 2 + this.table.hashCode();
        }

        byte var15 = 0;
        if (this.isOverlayDone()) {
            var15 = (byte)(var15 | 1);
        }

        if (this.haveRoof) {
            var15 = (byte)(var15 | 2);
        }

        if (this.burntOut) {
            var15 = (byte)(var15 | 4);
        }

        var1 = var1 * 2 + var15;
        var1 = var1 * 2 + this.getErosionData().hashCode();
        if (this.getTrapPositionX() > 0) {
            var1 = var1 * 2 + this.getTrapPositionX();
            var1 = var1 * 2 + this.getTrapPositionY();
            var1 = var1 * 2 + this.getTrapPositionZ();
        }

        var1 = var1 * 2 + (this.haveElectricity() ? 1 : 0);
        return var1 * 2 + (this.haveSheetRope ? 1 : 0);
    }

    public IsoGridSquare(IsoCell var1, SliceY var2, int var3, int var4, int var5) {
        this.ID = ++IDMax;
        this.x = var3;
        this.y = var4;
        this.z = var5;
        this.CachedScreenValue = -1;
        col = 0;
        path = 0;
        pathdoor = 0;
        vision = 0;
        this.collideMatrix = 134217727;
        this.pathMatrix = 134217727;
        this.visionMatrix = 0;

        for (int var6 = 0; var6 < 4; var6++) {
            if (GameServer.bServer) {
                if (var6 == 0) {
                    this.lighting[var6] = new ServerLighting();
                }
            } else if (LightingJNI.init) {
                this.lighting[var6] = new JNILighting(var6, this);
            } else {
                this.lighting[var6] = new Lighting();
            }
        }
    }

    public IsoGridSquare getTileInDirection(IsoDirections var1) {
        if (var1 == IsoDirections.N) {
            return this.getCell().getGridSquare(this.x, this.y - 1, this.z);
        } else if (var1 == IsoDirections.NE) {
            return this.getCell().getGridSquare(this.x + 1, this.y - 1, this.z);
        } else if (var1 == IsoDirections.NW) {
            return this.getCell().getGridSquare(this.x - 1, this.y - 1, this.z);
        } else if (var1 == IsoDirections.E) {
            return this.getCell().getGridSquare(this.x + 1, this.y, this.z);
        } else if (var1 == IsoDirections.W) {
            return this.getCell().getGridSquare(this.x - 1, this.y, this.z);
        } else if (var1 == IsoDirections.SE) {
            return this.getCell().getGridSquare(this.x + 1, this.y + 1, this.z);
        } else if (var1 == IsoDirections.SW) {
            return this.getCell().getGridSquare(this.x - 1, this.y + 1, this.z);
        } else if (var1 == IsoDirections.S) {
            return this.getCell().getGridSquare(this.x, this.y + 1, this.z);
        } else {
            return null;
        }
    }

    IsoObject getWall() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (var2 != null && var2.sprite != null && (var2.sprite.cutW || var2.sprite.cutN)) {
                return var2;
            }
        }

        return null;
    }

    public IsoObject getThumpableWall(boolean var1) {
        IsoObject var2 = this.getWall(var1);
        if (var2 != null && var2 instanceof IsoThumpable) {
            return var2;
        } else {
            return null;
        }
    }

    public IsoObject getHoppableWall(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (var3 != null && var3.sprite != null) {
                PropertyContainer var4 = var3.getProperties();
                boolean var5 = var4.Is(IsoFlagType.TallHoppableW) && !var4.Is(IsoFlagType.WallWTrans);
                boolean var6 = var4.Is(IsoFlagType.TallHoppableN) && !var4.Is(IsoFlagType.WallNTrans);
                if (var5 && !var1 || var6 && var1) {
                    return var3;
                }
            }
        }

        return null;
    }

    public IsoObject getThumpableWallOrHoppable(boolean var1) {
        IsoObject var2 = this.getThumpableWall(var1);
        IsoObject var3 = this.getHoppableWall(var1);
        if (var2 != null && var3 != null && var2 == var3) {
            return var2;
        } else if (var2 == null && var3 != null) {
            return var3;
        } else if (var2 != null && var3 == null) {
            return var2;
        } else {
            return null;
        }
    }

    public Boolean getWallFull() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (var2 != null
                && var2.sprite != null
                && (
                    var2.sprite.cutN
                        || var2.sprite.cutW
                        || var2.sprite.getProperties().Is(IsoFlagType.WallN)
                        || var2.sprite.getProperties().Is(IsoFlagType.WallW)
                )) {
                return true;
            }
        }

        return false;
    }

    public IsoObject getWall(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (var3 != null && var3.sprite != null && (var3.sprite.cutN && var1 || var3.sprite.cutW && !var1)) {
                return var3;
            }
        }

        return null;
    }

    public IsoObject getWallSE() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (var2 != null && var2.sprite != null && var2.sprite.getProperties().Is(IsoFlagType.WallSE)) {
                return var2;
            }
        }

        return null;
    }

    public IsoObject getFloor() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (var2.sprite != null && var2.sprite.getProperties().Is(IsoFlagType.solidfloor)) {
                return var2;
            }
        }

        return null;
    }

    public IsoObject getPlayerBuiltFloor() {
        if (this.getBuilding() == null && this.roofHideBuilding == null) {
            return this.getFloor();
        } else {
            return null;
        }
    }

    public void interpolateLight(ColorInfo var1, float var2, float var3) {
        IsoCell var4 = this.getCell();
        if (var2 < 0.0F) {
            var2 = 0.0F;
        }

        if (var2 > 1.0F) {
            var2 = 1.0F;
        }

        if (var3 < 0.0F) {
            var3 = 0.0F;
        }

        if (var3 > 1.0F) {
            var3 = 1.0F;
        }

        int var5 = IsoCamera.frameState.playerIndex;
        int var6 = this.getVertLight(0, var5);
        int var7 = this.getVertLight(1, var5);
        int var8 = this.getVertLight(2, var5);
        int var9 = this.getVertLight(3, var5);
        tl.fromColor(var6);
        bl.fromColor(var9);
        tr.fromColor(var7);
        br.fromColor(var8);
        tl.interp(tr, var2, interp1);
        bl.interp(br, var2, interp2);
        interp1.interp(interp2, var3, finalCol);
        var1.r = finalCol.r;
        var1.g = finalCol.g;
        var1.b = finalCol.b;
        var1.a = finalCol.a;
    }

    public void EnsureSurroundNotNull() {
        assert !GameServer.bServer;

        for (int var1 = -1; var1 <= 1; var1++) {
            for (int var2 = -1; var2 <= 1; var2++) {
                if ((var1 != 0 || var2 != 0)
                    && IsoWorld.instance.isValidSquare(this.x + var1, this.y + var2, this.z)
                    && this.getCell().getChunkForGridSquare(this.x + var1, this.y + var2, this.z) != null) {
                    IsoGridSquare var3 = this.getCell().getGridSquare(this.x + var1, this.y + var2, this.z);
                    if (var3 == null) {
                        var3 = getNew(this.getCell(), null, this.x + var1, this.y + var2, this.z);
                        IsoGridSquare var4 = this.getCell().ConnectNewSquare(var3, false);
                    }
                }
            }
        }
    }

    public IsoObject addFloor(String var1) {
        IsoRegions.setPreviousFlags(this);
        IsoObject var2 = new IsoObject(this.getCell(), this, var1);
        boolean var3 = false;

        for (int var4 = 0; var4 < this.getObjects().size(); var4++) {
            IsoObject var5 = (IsoObject)this.getObjects().get(var4);
            IsoSprite var6 = var5.sprite;
            if (var6 != null) {
                if (!var6.getProperties().Is(IsoFlagType.solidfloor)
                    && !var6.getProperties().Is(IsoFlagType.noStart)
                    && (!var6.getProperties().Is(IsoFlagType.vegitation) || var5.getType() == IsoObjectType.tree)
                    && (var6.getName() == null || !var6.getName().startsWith("blends_grassoverlays"))) {
                    continue;
                }

                if (var6.getName() != null && var6.getName().startsWith("floors_rugs")) {
                    var3 = true;
                } else {
                    this.transmitRemoveItemFromSquare(var5);
                    var4--;
                }
            }
        }

        var2.sprite.getProperties().Set(IsoFlagType.solidfloor);
        if (var3) {
            this.getObjects().add(0, var2);
        } else {
            this.getObjects().add(var2);
        }

        return null;
    }

    public IsoThumpable AddStairs(boolean var1, int var2, String var3, String var4, KahluaTable var5) {
        IsoRegions.setPreviousFlags(this);
        this.EnsureSurroundNotNull();
        boolean var6 = !this.TreatAsSolidFloor() && !this.HasStairsBelow();
        this.CachedIsFree = false;
        IsoThumpable var7 = new IsoThumpable(this.getCell(), this, var3, var1, var5);
        if (var1) {
            if (var2 == 0) {
                var7.setType(IsoObjectType.stairsBN);
            }

            if (var2 == 1) {
                var7.setType(IsoObjectType.stairsMN);
            }

            if (var2 == 2) {
                var7.setType(IsoObjectType.stairsTN);
                var7.sprite.getProperties().Set(var1 ? IsoFlagType.cutN : IsoFlagType.cutW);
            }
        }

        if (!var1) {
            if (var2 == 0) {
                var7.setType(IsoObjectType.stairsBW);
            }

            if (var2 == 1) {
                var7.setType(IsoObjectType.stairsMW);
            }

            if (var2 == 2) {
                var7.setType(IsoObjectType.stairsTW);
                var7.sprite.getProperties().Set(var1 ? IsoFlagType.cutN : IsoFlagType.cutW);
            }
        }

        this.AddSpecialObject(var7);
        if (var6 && var2 == 2) {
            int var8 = this.z - 1;
            IsoGridSquare var9 = this.getCell().getGridSquare(this.x, this.y, var8);
            if (var9 == null) {
                var9 = new IsoGridSquare(this.getCell(), null, this.x, this.y, var8);
                this.getCell().ConnectNewSquare(var9, true);
            }

            while (var8 >= 0) {
                IsoThumpable var10 = new IsoThumpable(this.getCell(), var9, var4, var1, var5);
                var9.AddSpecialObject(var10);
                var10.transmitCompleteItemToServer();
                if (var9.TreatAsSolidFloor()) {
                    break;
                }

                if (this.getCell().getGridSquare(var9.x, var9.y, --var8) == null) {
                    var9 = new IsoGridSquare(this.getCell(), null, var9.x, var9.y, var8);
                    this.getCell().ConnectNewSquare(var9, true);
                } else {
                    var9 = this.getCell().getGridSquare(var9.x, var9.y, var8);
                }
            }
        }

        if (var2 == 2) {
            IsoGridSquare var12 = null;
            if (var1) {
                if (IsoWorld.instance.isValidSquare(this.x, this.y - 1, this.z + 1)) {
                    var12 = this.getCell().getGridSquare(this.x, this.y - 1, this.z + 1);
                    if (var12 == null) {
                        var12 = new IsoGridSquare(this.getCell(), null, this.x, this.y - 1, this.z + 1);
                        this.getCell().ConnectNewSquare(var12, false);
                    }

                    if (!var12.Properties.Is(IsoFlagType.solidfloor)) {
                        var12.addFloor("carpentry_02_57");
                    }
                }
            } else if (IsoWorld.instance.isValidSquare(this.x - 1, this.y, this.z + 1)) {
                var12 = this.getCell().getGridSquare(this.x - 1, this.y, this.z + 1);
                if (var12 == null) {
                    var12 = new IsoGridSquare(this.getCell(), null, this.x - 1, this.y, this.z + 1);
                    this.getCell().ConnectNewSquare(var12, false);
                }

                if (!var12.Properties.Is(IsoFlagType.solidfloor)) {
                    var12.addFloor("carpentry_02_57");
                }
            }
        }

        for (int var15 = this.getX() - 1; var15 <= this.getX() + 1; var15++) {
            for (int var16 = this.getY() - 1; var16 <= this.getY() + 1; var16++) {
                for (int var17 = this.getZ() - 1; var17 <= this.getZ() + 1; var17++) {
                    if (IsoWorld.instance.isValidSquare(var15, var16, var17)) {
                        IsoGridSquare var11 = this.getCell().getGridSquare(var15, var16, var17);
                        if (var11 == null) {
                            var11 = new IsoGridSquare(this.getCell(), null, var15, var16, var17);
                            this.getCell().ConnectNewSquare(var11, false);
                        }

                        var11.ReCalculateCollide(this);
                        var11.ReCalculateVisionBlocked(this);
                        var11.ReCalculatePathFind(this);
                        this.ReCalculateCollide(var11);
                        this.ReCalculatePathFind(var11);
                        this.ReCalculateVisionBlocked(var11);
                        var11.CachedIsFree = false;
                    }
                }
            }
        }

        return var7;
    }

    void ReCalculateAll(IsoGridSquare var1) {
        this.ReCalculateAll(var1, cellGetSquare);
    }

    void ReCalculateAll(IsoGridSquare var1, GetSquare var2) {
        if (var1 != null && var1 != this) {
            this.SolidFloorCached = false;
            var1.SolidFloorCached = false;
            this.RecalcPropertiesIfNeeded();
            var1.RecalcPropertiesIfNeeded();
            this.ReCalculateCollide(var1, var2);
            var1.ReCalculateCollide(this, var2);
            this.ReCalculatePathFind(var1, var2);
            var1.ReCalculatePathFind(this, var2);
            this.ReCalculateVisionBlocked(var1, var2);
            var1.ReCalculateVisionBlocked(this, var2);
            this.setBlockedGridPointers(var2);
            var1.setBlockedGridPointers(var2);
        }
    }

    void ReCalculateAll(boolean var1, IsoGridSquare var2, GetSquare var3) {
        if (var2 != null && var2 != this) {
            this.SolidFloorCached = false;
            var2.SolidFloorCached = false;
            this.RecalcPropertiesIfNeeded();
            if (var1) {
                var2.RecalcPropertiesIfNeeded();
            }

            this.ReCalculateCollide(var2, var3);
            if (var1) {
                var2.ReCalculateCollide(this, var3);
            }

            this.ReCalculatePathFind(var2, var3);
            if (var1) {
                var2.ReCalculatePathFind(this, var3);
            }

            this.ReCalculateVisionBlocked(var2, var3);
            if (var1) {
                var2.ReCalculateVisionBlocked(this, var3);
            }

            this.setBlockedGridPointers(var3);
            if (var1) {
                var2.setBlockedGridPointers(var3);
            }
        }
    }

    void ReCalculateMineOnly(IsoGridSquare var1) {
        this.SolidFloorCached = false;
        this.RecalcProperties();
        this.ReCalculateCollide(var1);
        this.ReCalculatePathFind(var1);
        this.ReCalculateVisionBlocked(var1);
        this.setBlockedGridPointers(cellGetSquare);
    }

    public void RecalcAllWithNeighbours(boolean var1) {
        this.RecalcAllWithNeighbours(var1, cellGetSquare);
    }

    public void RecalcAllWithNeighbours(boolean var1, GetSquare var2) {
        this.SolidFloorCached = false;
        this.RecalcPropertiesIfNeeded();

        for (int var3 = this.getX() - 1; var3 <= this.getX() + 1; var3++) {
            for (int var4 = this.getY() - 1; var4 <= this.getY() + 1; var4++) {
                for (int var5 = this.getZ() - 1; var5 <= this.getZ() + 1; var5++) {
                    if (IsoWorld.instance.isValidSquare(var3, var4, var5)) {
                        int var6 = var3 - this.getX();
                        int var7 = var4 - this.getY();
                        int var8 = var5 - this.getZ();
                        if (var6 == 0 && var7 == 0 && var8 == 0) {
                            continue;
                        }

                        IsoGridSquare var9 = var2.getGridSquare(var3, var4, var5);
                        if (var9 != null) {
                            var9.DirtySlice();
                            this.ReCalculateAll(var1, var9, var2);
                        }
                    }
                }
            }
        }

        IsoWorld.instance.CurrentCell.DoGridNav(this, var2);
        IsoGridSquare var10 = this.nav[IsoDirections.N.index()];
        IsoGridSquare var11 = this.nav[IsoDirections.S.index()];
        IsoGridSquare var12 = this.nav[IsoDirections.W.index()];
        IsoGridSquare var13 = this.nav[IsoDirections.E.index()];
        if (var10 != null && var12 != null) {
            var10.ReCalculateAll(var12, var2);
        }

        if (var10 != null && var13 != null) {
            var10.ReCalculateAll(var13, var2);
        }

        if (var11 != null && var12 != null) {
            var11.ReCalculateAll(var12, var2);
        }

        if (var11 != null && var13 != null) {
            var11.ReCalculateAll(var13, var2);
        }
    }

    public void RecalcAllWithNeighboursMineOnly() {
        this.SolidFloorCached = false;
        this.RecalcProperties();

        for (int var1 = this.getX() - 1; var1 <= this.getX() + 1; var1++) {
            for (int var2 = this.getY() - 1; var2 <= this.getY() + 1; var2++) {
                for (int var3 = this.getZ() - 1; var3 <= this.getZ() + 1; var3++) {
                    if (var3 >= 0) {
                        int var4 = var1 - this.getX();
                        int var5 = var2 - this.getY();
                        int var6 = var3 - this.getZ();
                        if (var4 == 0 && var5 == 0 && var6 == 0) {
                            continue;
                        }

                        IsoGridSquare var7 = this.getCell().getGridSquare(var1, var2, var3);
                        if (var7 != null) {
                            var7.DirtySlice();
                            this.ReCalculateMineOnly(var7);
                        }
                    }
                }
            }
        }
    }

    boolean IsWindow(int var1, int var2, int var3) {
        IsoGridSquare var4 = this.getCell().getGridSquare(this.x + var1, this.y + var2, this.z + var3);
        return this.getWindowTo(var4) != null || this.getWindowThumpableTo(var4) != null;
    }

    void RemoveAllWith(IsoFlagType var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (var3.sprite != null && var3.sprite.getProperties().Is(var1)) {
                this.Objects.remove(var3);
                this.SpecialObjects.remove(var3);
                var2--;
            }
        }

        this.RecalcAllWithNeighbours(true);
    }

    public boolean hasSupport() {
        IsoGridSquare var1 = this.getCell().getGridSquare(this.x, this.y + 1, this.z);
        IsoGridSquare var2 = this.getCell().getGridSquare(this.x + 1, this.y, this.z);

        for (int var3 = 0; var3 < this.Objects.size(); var3++) {
            IsoObject var4 = (IsoObject)this.Objects.get(var3);
            if (var4.sprite != null
                && (
                    var4.sprite.getProperties().Is(IsoFlagType.solid)
                        || (var4.sprite.getProperties().Is(IsoFlagType.cutW) || var4.sprite.getProperties().Is(IsoFlagType.cutN))
                            && !var4.sprite.Properties.Is(IsoFlagType.halfheight)
                )) {
                return true;
            }
        }

        if (var1 != null && var1.Properties.Is(IsoFlagType.cutN) && !var1.Properties.Is(IsoFlagType.halfheight)) {
            return true;
        } else if (var2 != null && var2.Properties.Is(IsoFlagType.cutW) && !var1.Properties.Is(IsoFlagType.halfheight)) {
            return true;
        } else {
            return false;
        }
    }

    public Integer getID() {
        return this.ID;
    }

    public void setID(int var1) {
        this.ID = var1;
    }

    private int savematrix(boolean[][][] var1, byte[] var2, int var3) {
        for (int var4 = 0; var4 <= 2; var4++) {
            for (int var5 = 0; var5 <= 2; var5++) {
                for (int var6 = 0; var6 <= 2; var6++) {
                    var2[var3] = (byte)(var1[var4][var5][var6] ? 1 : 0);
                    var3++;
                }
            }
        }

        return var3;
    }

    private int loadmatrix(boolean[][][] var1, byte[] var2, int var3) {
        for (int var4 = 0; var4 <= 2; var4++) {
            for (int var5 = 0; var5 <= 2; var5++) {
                for (int var6 = 0; var6 <= 2; var6++) {
                    var1[var4][var5][var6] = var2[var3] != 0;
                    var3++;
                }
            }
        }

        return var3;
    }

    private void savematrix(boolean[][][] var1, ByteBuffer var2) {
        for (int var3 = 0; var3 <= 2; var3++) {
            for (int var4 = 0; var4 <= 2; var4++) {
                for (int var5 = 0; var5 <= 2; var5++) {
                    var2.put((byte)(var1[var3][var4][var5] ? 1 : 0));
                }
            }
        }
    }

    private void loadmatrix(boolean[][][] var1, ByteBuffer var2) {
        for (int var3 = 0; var3 <= 2; var3++) {
            for (int var4 = 0; var4 <= 2; var4++) {
                for (int var5 = 0; var5 <= 2; var5++) {
                    var1[var3][var4][var5] = var2.get() != 0;
                }
            }
        }
    }

    public void DirtySlice() {
    }

    public void setHourSeenToCurrent() {
        this.hourLastSeen = (int)GameTime.instance.getWorldAgeHours();
    }

    public void splatBlood(int var1, float var2) {
        var2 = var2 * 2.0F;
        var2 = var2 * 3.0F;
        if (var2 > 1.0F) {
            var2 = 1.0F;
        }

        IsoGridSquare var3 = this;
        IsoGridSquare var4 = this;

        for (int var5 = 0; var5 < var1; var5++) {
            if (var3 != null) {
                var3 = this.getCell().getGridSquare(this.getX(), this.getY() - var5, this.getZ());
            }

            if (var4 != null) {
                var4 = this.getCell().getGridSquare(this.getX() - var5, this.getY(), this.getZ());
            }

            float var6 = 0.0F;
            if (var4 != null && var4.testCollideAdjacent(null, -1, 0, 0)) {
                boolean var7 = false;
                boolean var8 = false;
                byte var9 = 0;
                byte var10 = 0;
                if (var4.getS() != null && var4.getS().testCollideAdjacent(null, -1, 0, 0)) {
                    var7 = true;
                }

                if (var4.getN() != null && var4.getN().testCollideAdjacent(null, -1, 0, 0)) {
                    var8 = true;
                }

                if (var7) {
                    var9 = -1;
                }

                if (var8) {
                    var10 = 1;
                }

                int var11 = var10 - var9;
                boolean var12 = false;
                byte var13 = 0;
                byte var14 = 0;
                if (var11 > 0 && Rand.Next(2) == 0) {
                    var12 = true;
                    if (var11 > 1) {
                        if (Rand.Next(2) == 0) {
                            var13 = -1;
                            var14 = 0;
                        } else {
                            var13 = 0;
                            var14 = 1;
                        }
                    } else {
                        var13 = var9;
                        var14 = var10;
                    }
                }

                float var15;
                IsoGridSquare var16;
                IsoGridSquare var17;
                label190: {
                    var15 = (float)Rand.Next(100) / 300.0F;
                    var16 = this.getCell().getGridSquare(var4.getX(), var4.getY() + var13, var4.getZ());
                    var17 = this.getCell().getGridSquare(var4.getX(), var4.getY() + var14, var4.getZ());
                    if (var16 != null
                        && var17 != null
                        && var16.Is(IsoFlagType.cutW)
                        && var17.Is(IsoFlagType.cutW)
                        && !var16.getProperties().Is(IsoFlagType.WallSE)
                        && !var17.getProperties().Is(IsoFlagType.WallSE)
                        && !var16.Is(IsoFlagType.HoppableW)
                        && !var17.Is(IsoFlagType.HoppableW)) {
                        break label190;
                    }

                    var12 = false;
                }

                if (var12) {
                    int var32 = 24 + Rand.Next(2) * 2;
                    if (Rand.Next(2) == 0) {
                        var32 += 8;
                    }

                    var16.DoSplat("overlay_blood_wall_01_" + (var32 + 1), false, IsoFlagType.cutW, var6, var15, var2);
                    var17.DoSplat("overlay_blood_wall_01_" + (var32 + 0), false, IsoFlagType.cutW, var6, var15, var2);
                } else {
                    int var18 = 0;
                    label133:
                    switch (Rand.Next(3)) {
                        case 0:
                            var18 = 0 + Rand.Next(4);
                        case 1:
                            var18 = 8 + Rand.Next(4);
                        case 2:
                            var18 = 16 + Rand.Next(4);
                    }
                }

                var4 = null;
            }

            if (var3 != null && var3.testCollideAdjacent(null, 0, -1, 0)) {
                boolean var21 = false;
                boolean var22 = false;
                byte var23 = 0;
                byte var24 = 0;
                if (var3.getW() != null && var3.getW().testCollideAdjacent(null, 0, -1, 0)) {
                    var21 = true;
                }

                if (var3.getE() != null && var3.getE().testCollideAdjacent(null, 0, -1, 0)) {
                    var22 = true;
                }

                if (var21) {
                    var23 = -1;
                }

                if (var22) {
                    var24 = 1;
                }

                int var25 = var24 - var23;
                boolean var26 = false;
                byte var27 = 0;
                byte var28 = 0;
                if (var25 > 0 && Rand.Next(2) == 0) {
                    var26 = true;
                    if (var25 > 1) {
                        if (Rand.Next(2) == 0) {
                            var27 = -1;
                            var28 = 0;
                        } else {
                            var27 = 0;
                            var28 = 1;
                        }
                    } else {
                        var27 = var23;
                        var28 = var24;
                    }
                }

                float var29;
                IsoGridSquare var30;
                IsoGridSquare var31;
                label159: {
                    var29 = (float)Rand.Next(100) / 300.0F;
                    var30 = this.getCell().getGridSquare(var3.getX() + var27, var3.getY(), var3.getZ());
                    var31 = this.getCell().getGridSquare(var3.getX() + var28, var3.getY(), var3.getZ());
                    if (var30 != null
                        && var31 != null
                        && var30.Is(IsoFlagType.cutN)
                        && var31.Is(IsoFlagType.cutN)
                        && !var30.getProperties().Is(IsoFlagType.WallSE)
                        && !var31.getProperties().Is(IsoFlagType.WallSE)
                        && !var30.Is(IsoFlagType.HoppableN)
                        && !var31.Is(IsoFlagType.HoppableN)) {
                        break label159;
                    }

                    var26 = false;
                }

                if (var26) {
                    int var34 = 28 + Rand.Next(2) * 2;
                    if (Rand.Next(2) == 0) {
                        var34 += 8;
                    }

                    var30.DoSplat("overlay_blood_wall_01_" + (var34 + 0), false, IsoFlagType.cutN, var6, var29, var2);
                    var31.DoSplat("overlay_blood_wall_01_" + (var34 + 1), false, IsoFlagType.cutN, var6, var29, var2);
                } else {
                    int var33 = 0;
                    label120:
                    switch (Rand.Next(3)) {
                        case 0:
                            var33 = 4 + Rand.Next(4);
                        case 1:
                            var33 = 12 + Rand.Next(4);
                        case 2:
                            var33 = 20 + Rand.Next(4);
                    }
                }

                var3 = null;
            }
        }
    }

    public boolean haveBlood() {
        if (Core.OptionBloodDecals == 0) {
            return false;
        } else {
            for (int var1 = 0; var1 < this.getObjects().size(); var1++) {
                IsoObject var2 = (IsoObject)this.getObjects().get(var1);
                if (var2.wallBloodSplats != null && !var2.wallBloodSplats.isEmpty()) {
                    return true;
                }
            }

            for (int var5 = 0; var5 < this.getChunk().FloorBloodSplats.size(); var5++) {
                IsoFloorBloodSplat var6 = (IsoFloorBloodSplat)this.getChunk().FloorBloodSplats.get(var5);
                float var3 = var6.x + (float)(this.getChunk().wx * 10);
                float var4 = var6.y + (float)(this.getChunk().wy * 10);
                if ((int)var3 - 1 <= this.x && (int)var3 + 1 >= this.x && (int)var4 - 1 <= this.y && (int)var4 + 1 >= this.y) {
                    return true;
                }
            }

            return false;
        }
    }

    public void removeBlood(boolean var1, boolean var2) {
        for (int var3 = 0; var3 < this.getObjects().size(); var3++) {
            IsoObject var4 = (IsoObject)this.getObjects().get(var3);
            if (var4.wallBloodSplats != null) {
                var4.wallBloodSplats.clear();
            }
        }

        if (!var2) {
            for (int var7 = 0; var7 < this.getChunk().FloorBloodSplats.size(); var7++) {
                IsoFloorBloodSplat var9 = (IsoFloorBloodSplat)this.getChunk().FloorBloodSplats.get(var7);
                int var5 = (int)((float)(this.getChunk().wx * 10) + var9.x);
                int var6 = (int)((float)(this.getChunk().wy * 10) + var9.y);
                if (var5 >= this.getX() - 1 && var5 <= this.getX() + 1 && var6 >= this.getY() - 1 && var6 <= this.getY() + 1) {
                    this.getChunk().FloorBloodSplats.remove(var7);
                    var7--;
                }
            }
        }

        if (GameClient.bClient && !var1) {
            ByteBufferWriter var8 = GameClient.connection.startPacket();
            PacketType.RemoveBlood.doPacket(var8);
            var8.putInt(this.x);
            var8.putInt(this.y);
            var8.putInt(this.z);
            var8.putBoolean(var2);
            PacketType.RemoveBlood.send(GameClient.connection);
        }
    }

    public void DoSplat(String var1, boolean var2, IsoFlagType var3, float var4, float var5, float var6) {
        for (int var7 = 0; var7 < this.getObjects().size(); var7++) {
            IsoObject var8 = (IsoObject)this.getObjects().get(var7);
            if (var8.sprite != null && var8.sprite.getProperties().Is(var3)) {
                if (var8 instanceof IsoWindow && var8.isDestroyed()) {
                    continue;
                }

                IsoSprite var9 = IsoSprite.getSprite(IsoSpriteManager.instance, var1, 0);
                if (var9 == null) {
                    return;
                }

                if (var8.wallBloodSplats == null) {
                    var8.wallBloodSplats = new ArrayList();
                }

                IsoWallBloodSplat var10 = new IsoWallBloodSplat((float)GameTime.getInstance().getWorldAgeHours(), var9);
                var8.wallBloodSplats.add(var10);
            }
        }
    }

    public void ClearTileObjects() {
        this.Objects.clear();
        this.RecalcProperties();
    }

    public void ClearTileObjectsExceptFloor() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (var2.sprite != null && var2.sprite.getProperties().Is(IsoFlagType.solidfloor)) {
                continue;
            }

            this.Objects.remove(var2);
            var1--;
        }

        this.RecalcProperties();
    }

    public int RemoveTileObject(IsoObject var1) {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:62
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:310)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 000: aload 0
        // 001: invokestatic zombie/iso/areas/isoregion/IsoRegions.setPreviousFlags (Lzombie/iso/IsoGridSquare;)V
        // 004: aload 0
        // 005: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 008: aload 1
        // 009: invokevirtual zombie/util/list/PZArrayList.indexOf (Ljava/lang/Object;)I
        // 00c: istore 2
        // 00d: aload 0
        // 00e: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 011: aload 1
        // 012: invokevirtual zombie/util/list/PZArrayList.contains (Ljava/lang/Object;)Z
        // 015: ifne 021
        // 018: aload 0
        // 019: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 01c: aload 1
        // 01d: invokevirtual java/util/ArrayList.indexOf (Ljava/lang/Object;)I
        // 020: istore 2
        // 021: aload 1
        // 022: ifnull 13b
        // 025: aload 0
        // 026: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 029: aload 1
        // 02a: invokevirtual zombie/util/list/PZArrayList.contains (Ljava/lang/Object;)Z
        // 02d: ifeq 13b
        // 030: aload 1
        // 031: invokevirtual zombie/iso/IsoObject.isTableSurface ()Z
        // 034: ifeq 08b
        // 037: aload 0
        // 038: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 03b: aload 1
        // 03c: invokevirtual zombie/util/list/PZArrayList.indexOf (Ljava/lang/Object;)I
        // 03f: bipush 1
        // 040: iadd
        // 041: istore 3
        // 042: iload 3
        // 043: aload 0
        // 044: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 047: invokevirtual zombie/util/list/PZArrayList.size ()I
        // 04a: if_icmpge 08b
        // 04d: aload 0
        // 04e: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 051: iload 3
        // 052: invokevirtual zombie/util/list/PZArrayList.get (I)Ljava/lang/Object;
        // 055: checkcast zombie/iso/IsoObject
        // 058: astore 4
        // 05a: aload 4
        // 05c: invokevirtual zombie/iso/IsoObject.isTableTopObject ()Z
        // 05f: ifne 06a
        // 062: aload 4
        // 064: invokevirtual zombie/iso/IsoObject.isTableSurface ()Z
        // 067: ifeq 085
        // 06a: aload 4
        // 06c: aload 4
        // 06e: invokevirtual zombie/iso/IsoObject.getRenderYOffset ()F
        // 071: aload 1
        // 072: invokevirtual zombie/iso/IsoObject.getSurfaceOffset ()F
        // 075: fsub
        // 076: invokevirtual zombie/iso/IsoObject.setRenderYOffset (F)V
        // 079: aload 4
        // 07b: fconst_0
        // 07c: putfield zombie/iso/IsoObject.sx F
        // 07f: aload 4
        // 081: fconst_0
        // 082: putfield zombie/iso/IsoObject.sy F
        // 085: iinc 3 1
        // 088: goto 042
        // 08b: aload 0
        // 08c: invokevirtual zombie/iso/IsoGridSquare.getPlayerBuiltFloor ()Lzombie/iso/IsoObject;
        // 08f: astore 3
        // 090: aload 1
        // 091: aload 3
        // 092: if_acmpne 098
        // 095: invokestatic zombie/iso/IsoGridOcclusionData.SquareChanged ()V
        // 098: ldc_w "OnObjectAboutToBeRemoved"
        // 09b: aload 1
        // 09c: invokestatic zombie/Lua/LuaEventManager.triggerEvent (Ljava/lang/String;Ljava/lang/Object;)V
        // 09f: aload 0
        // 0a0: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 0a3: aload 1
        // 0a4: invokevirtual zombie/util/list/PZArrayList.contains (Ljava/lang/Object;)Z
        // 0a7: ifne 0b5
        // 0aa: new java/lang/IllegalArgumentException
        // 0ad: dup
        // 0ae: ldc_w "OnObjectAboutToBeRemoved not allowed to remove the object"
        // 0b1: invokespecial java/lang/IllegalArgumentException.<init> (Ljava/lang/String;)V
        // 0b4: athrow
        // 0b5: aload 0
        // 0b6: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 0b9: aload 1
        // 0ba: invokevirtual zombie/util/list/PZArrayList.indexOf (Ljava/lang/Object;)I
        // 0bd: istore 2
        // 0be: aload 1
        // 0bf: invokevirtual zombie/iso/IsoObject.removeFromWorld ()V
        // 0c2: aload 1
        // 0c3: invokevirtual zombie/iso/IsoObject.removeFromSquare ()V
        // 0c6: getstatic zombie/iso/IsoGridSquare.$assertionsDisabled Z
        // 0c9: ifne 0df
        // 0cc: aload 0
        // 0cd: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 0d0: aload 1
        // 0d1: invokevirtual zombie/util/list/PZArrayList.contains (Ljava/lang/Object;)Z
        // 0d4: ifeq 0df
        // 0d7: new java/lang/AssertionError
        // 0da: dup
        // 0db: invokespecial java/lang/AssertionError.<init> ()V
        // 0de: athrow
        // 0df: getstatic zombie/iso/IsoGridSquare.$assertionsDisabled Z
        // 0e2: ifne 0f8
        // 0e5: aload 0
        // 0e6: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 0e9: aload 1
        // 0ea: invokevirtual java/util/ArrayList.contains (Ljava/lang/Object;)Z
        // 0ed: ifeq 0f8
        // 0f0: new java/lang/AssertionError
        // 0f3: dup
        // 0f4: invokespecial java/lang/AssertionError.<init> ()V
        // 0f7: athrow
        // 0f8: aload 1
        // 0f9: instanceof zombie/iso/objects/IsoWorldInventoryObject
        // 0fc: ifne 137
        // 0ff: aload 0
        // 100: bipush 1
        // 101: invokevirtual zombie/iso/IsoGridSquare.RecalcAllWithNeighbours (Z)V
        // 104: aload 0
        // 105: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 108: aload 0
        // 109: invokevirtual zombie/iso/IsoGridSquare.getX ()I
        // 10c: aload 0
        // 10d: invokevirtual zombie/iso/IsoGridSquare.getY ()I
        // 110: invokevirtual zombie/iso/IsoCell.checkHaveRoof (II)V
        // 113: bipush 0
        // 114: istore 4
        // 116: iload 4
        // 118: getstatic zombie/characters/IsoPlayer.numPlayers I
        // 11b: if_icmpge 12b
        // 11e: getstatic zombie/iso/LosUtil.cachecleared [Z
        // 121: iload 4
        // 123: bipush 1
        // 124: bastore
        // 125: iinc 4 1
        // 128: goto 116
        // 12b: bipush -1
        // 12c: invokestatic zombie/iso/IsoGridSquare.setRecalcLightTime (I)V
        // 12f: getstatic zombie/GameTime.instance Lzombie/GameTime;
        // 132: ldc 100.0
        // 134: putfield zombie/GameTime.lightSourceUpdate F
        // 137: aload 0
        // 138: invokevirtual zombie/iso/IsoGridSquare.fixPlacedItemRenderOffsets ()V
        // 13b: getstatic zombie/MapCollisionData.instance Lzombie/MapCollisionData;
        // 13e: aload 0
        // 13f: invokevirtual zombie/MapCollisionData.squareChanged (Lzombie/iso/IsoGridSquare;)V
        // 142: ldc_w "OnTileRemoved"
        // 145: aload 1
        // 146: invokestatic zombie/Lua/LuaEventManager.triggerEvent (Ljava/lang/String;Ljava/lang/Object;)V
        // 149: getstatic zombie/vehicles/PolygonalMap2.instance Lzombie/vehicles/PolygonalMap2;
        // 14c: aload 0
        // 14d: invokevirtual zombie/vehicles/PolygonalMap2.squareChanged (Lzombie/iso/IsoGridSquare;)V
        // 150: aload 0
        // 151: bipush 1
        // 152: invokestatic zombie/iso/areas/isoregion/IsoRegions.squareChanged (Lzombie/iso/IsoGridSquare;Z)V
        // 155: iload 2
        // 156: ireturn
        return 0;
    }

    public int RemoveTileObjectErosionNoRecalc(IsoObject var1) {
        int var2 = this.Objects.indexOf(var1);
        IsoGridSquare var3 = var1.square;
        var1.removeFromWorld();
        var1.removeFromSquare();
        var3.RecalcPropertiesIfNeeded();

        assert !this.Objects.contains(var1);

        assert !this.SpecialObjects.contains(var1);

        return var2;
    }

    public void AddSpecialObject(IsoObject var1) {
        this.AddSpecialObject(var1, -1);
    }

    public void AddSpecialObject(IsoObject var1, int var2) {
        if (var1 != null) {
            IsoRegions.setPreviousFlags(this);
            var2 = this.placeWallAndDoorCheck(var1, var2);
            if (var2 != -1 && var2 >= 0 && var2 <= this.Objects.size()) {
                this.Objects.add(var2, var1);
            } else {
                this.Objects.add(var1);
            }
        }
    }

    public void AddTileObject(IsoObject var1) {
        this.AddTileObject(var1, -1);
    }

    public void AddTileObject(IsoObject var1, int var2) {
        if (var1 != null) {
            IsoRegions.setPreviousFlags(this);
            var2 = this.placeWallAndDoorCheck(var1, var2);
            if (var2 != -1 && var2 >= 0 && var2 <= this.Objects.size()) {
                this.Objects.add(var2, var1);
            } else {
                this.Objects.add(var1);
            }
        }
    }

    public int placeWallAndDoorCheck(IsoObject var1, int var2) {
        int var4 = -1;
        if (var1.sprite == null) {
            return var2;
        } else {
            IsoObjectType var3 = var1.sprite.getType();
            boolean var5 = var3 == IsoObjectType.doorN || var3 == IsoObjectType.doorW;
            boolean var6 = !var5
                && (var1.sprite.cutW || var1.sprite.cutN || var3 == IsoObjectType.doorFrN || var3 == IsoObjectType.doorFrW || var1.sprite.treatAsWallOrder);
            if (!var6 && !var5) {
                return var2;
            } else {
                int var8 = 0;

                while (var8 < this.Objects.size()) {
                    IsoObject var7 = (IsoObject)this.Objects.get(var8);
                    var3 = IsoObjectType.MAX;
                    if (var7.sprite != null) {
                        var3 = var7.sprite.getType();
                        if (!var6 || var3 != IsoObjectType.doorN && var3 != IsoObjectType.doorW) {
                        }

                        var4 = var8;
                    }

                    var8++;
                    continue;
                }

                return var2;
            }
        }
    }

    public void transmitAddObjectToSquare(IsoObject var1, int var2) {
        if (var1 != null && !this.Objects.contains(var1)) {
            this.AddTileObject(var1, var2);
            if (GameClient.bClient) {
                var1.transmitCompleteItemToServer();
            }

            if (GameServer.bServer) {
                var1.transmitCompleteItemToClients();
            }
        }
    }

    public int transmitRemoveItemFromSquare(IsoObject var1) {
        if (var1 != null && this.Objects.contains(var1)) {
            if (GameClient.bClient) {
                try {
                    GameClient.instance.checkAddedRemovedItems(var1);
                } catch (Exception var3) {
                    GameClient.connection.cancelPacket();
                    ExceptionLogger.logException(var3);
                }
            }

            if (GameServer.bServer) {
                return GameServer.RemoveItemFromMap(var1);
            } else {
                return this.RemoveTileObject(var1);
            }
        } else {
            return -1;
        }
    }

    public void transmitRemoveItemFromSquareOnServer(IsoObject var1) {
        if (var1 != null && this.Objects.contains(var1)) {
            if (GameServer.bServer) {
                GameServer.RemoveItemFromMap(var1);
            }
        }
    }

    public void transmitModdata() {
        if (GameClient.bClient) {
            ByteBufferWriter var1 = GameClient.connection.startPacket();
            PacketType.SendModData.doPacket(var1);
            var1.putInt(this.getX());
            var1.putInt(this.getY());
            var1.putInt(this.getZ());

            try {
                this.getModData().save(var1.bb);
            } catch (IOException var3) {
                var3.printStackTrace();
            }
        } else if (GameServer.bServer) {
            GameServer.loadModData(this);
        }
    }

    public void AddWorldInventoryItem(String var1, float var2, float var3, float var4, int var5) {
        for (int var6 = 0; var6 < var5; var6++) {
            this.AddWorldInventoryItem(var1, var2, var3, var4);
        }
    }

    public InventoryItem AddWorldInventoryItem(String var1, float var2, float var3, float var4) {
        InventoryItem var5 = InventoryItemFactory.CreateItem(var1);
        if (var5 == null) {
            return null;
        } else {
            IsoWorldInventoryObject var6 = new IsoWorldInventoryObject(var5, this, var2, var3, var4);
            var5.setAutoAge();
            var5.setWorldItem(var6);
            var6.setKeyId(var5.getKeyId());
            var6.setName(var5.getName());
            this.Objects.add(var6);
            this.WorldObjects.add(var6);
            var6.square.chunk.recalcHashCodeObjects();
            if (GameClient.bClient) {
                var6.transmitCompleteItemToServer();
            }

            if (GameServer.bServer) {
                var6.transmitCompleteItemToClients();
            }

            return var5;
        }
    }

    public InventoryItem AddWorldInventoryItem(InventoryItem var1, float var2, float var3, float var4) {
        return this.AddWorldInventoryItem(var1, var2, var3, var4, true);
    }

    public InventoryItem AddWorldInventoryItem(InventoryItem var1, float var2, float var3, float var4, boolean var5) {
        if (!var1.getFullType().contains(".Corpse")) {
            if (var1.getFullType().contains(".Generator")) {
                new IsoGenerator(var1, IsoWorld.instance.CurrentCell, this);
                return var1;
            } else {
                IsoWorldInventoryObject var14 = new IsoWorldInventoryObject(var1, this, var2, var3, var4);
                var14.setName(var1.getName());
                var14.setKeyId(var1.getKeyId());
                this.Objects.add(var14);
                this.WorldObjects.add(var14);
                var14.square.chunk.recalcHashCodeObjects();
                var1.setWorldItem(var14);
                var14.addToWorld();
                if (var5) {
                    if (GameClient.bClient) {
                        var14.transmitCompleteItemToServer();
                    }

                    if (GameServer.bServer) {
                        var14.transmitCompleteItemToClients();
                    }
                }

                return var1;
            }
        } else if (var1.byteData == null) {
            IsoZombie var13 = new IsoZombie(IsoWorld.instance.CurrentCell);
            var13.setDir(IsoDirections.fromIndex(Rand.Next(8)));
            var13.getForwardDirection().set(var13.dir.ToVector());
            var13.setFakeDead(false);
            var13.setHealth(0.0F);
            var13.upKillCount = false;
            var13.setX((float)this.x + var2);
            var13.setY((float)this.y + var3);
            var13.setZ((float)this.z);
            var13.square = this;
            var13.current = this;
            var13.dressInRandomOutfit();
            var13.DoZombieInventory();
            IsoDeadBody var15 = new IsoDeadBody(var13, true);
            this.addCorpse(var15, false);
            if (GameServer.bServer) {
                GameServer.sendCorpse(var15);
            }

            return var1;
        } else {
            IsoDeadBody var6 = new IsoDeadBody(IsoWorld.instance.CurrentCell);

            try {
                byte var7 = var1.byteData.get();
                byte var16 = var1.byteData.get();
                byte var9 = var1.byteData.get();
                byte var10 = var1.byteData.get();
                int var11 = 56;
                if (var7 == 87 && var16 == 86 && var9 == 69 && var10 == 82) {
                    var11 = var1.byteData.getInt();
                } else {
                    var1.byteData.rewind();
                }
            } catch (IOException var12) {
                var12.printStackTrace();
                IsoZombie var8 = new IsoZombie(null);
                var8.dir = var6.dir;
                var8.current = this;
                var8.x = var6.x;
                var8.y = var6.y;
                var8.z = var6.z;
                var6 = new IsoDeadBody(var8);
            }
        }

        return null;
    }

    public void restackSheetRope() {
        if (this.Is(IsoFlagType.climbSheetW) || this.Is(IsoFlagType.climbSheetN) || this.Is(IsoFlagType.climbSheetE) || this.Is(IsoFlagType.climbSheetS)) {
            for (int var1 = 0; var1 < this.getObjects().size() - 1; var1++) {
                IsoObject var2 = (IsoObject)this.getObjects().get(var1);
                if (var2.getProperties() == null
                    || !var2.getProperties().Is(IsoFlagType.climbSheetW)
                        && !var2.getProperties().Is(IsoFlagType.climbSheetN)
                        && !var2.getProperties().Is(IsoFlagType.climbSheetE)
                        && !var2.getProperties().Is(IsoFlagType.climbSheetS)) {
                    continue;
                }

                if (GameServer.bServer) {
                    this.transmitRemoveItemFromSquare(var2);
                    this.Objects.add(var2);
                    var2.transmitCompleteItemToClients();
                } else if (!GameClient.bClient) {
                    this.Objects.remove(var2);
                    this.Objects.add(var2);
                }
                break;
            }
        }
    }

    public void Burn() {
        if (!GameServer.bServer && !GameClient.bClient || !ServerOptions.instance.NoFire.getValue()) {
            if (this.getCell() != null) {
                this.BurnWalls(true);
                LuaEventManager.triggerEvent("OnGridBurnt", this);
            }
        }
    }

    public void Burn(boolean var1) {
        if (!GameServer.bServer && !GameClient.bClient || !ServerOptions.instance.NoFire.getValue()) {
            if (this.getCell() != null) {
                this.BurnWalls(var1);
            }
        }
    }

    public void BurnWalls(boolean var1) {
        if (!GameClient.bClient) {
            if (GameServer.bServer && SafeHouse.isSafeHouse(this, null, false) != null) {
                if (ServerOptions.instance.NoFire.getValue()) {
                    return;
                }

                if (!ServerOptions.instance.SafehouseAllowFire.getValue()) {
                    return;
                }
            }

            for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
                IsoObject var3 = this.SpecialObjects.get(var2);
                if (var3 instanceof IsoThumpable && ((IsoThumpable)var3).haveSheetRope()) {
                    ((IsoThumpable)var3).removeSheetRope(null);
                }

                if (var3 instanceof IsoWindow) {
                    if (((IsoWindow)var3).haveSheetRope()) {
                        ((IsoWindow)var3).removeSheetRope(null);
                    }

                    ((IsoWindow)var3).removeSheet(null);
                }

                if (IsoWindowFrame.isWindowFrame(var3) && IsoWindowFrame.haveSheetRope(var3)) {
                    IsoWindowFrame.removeSheetRope(var3, null);
                }

                if (var3 instanceof BarricadeAble) {
                    IsoBarricade var4 = ((BarricadeAble)var3).getBarricadeOnSameSquare();
                    IsoBarricade var5 = ((BarricadeAble)var3).getBarricadeOnOppositeSquare();
                    if (var4 != null) {
                        if (GameServer.bServer) {
                            GameServer.RemoveItemFromMap(var4);
                        } else {
                            this.RemoveTileObject(var4);
                        }
                    }

                    if (var5 != null) {
                        if (GameServer.bServer) {
                            GameServer.RemoveItemFromMap(var5);
                        } else {
                            var5.getSquare().RemoveTileObject(var5);
                        }
                    }
                }
            }

            this.SpecialObjects.clear();
            boolean var10 = false;
            if (!this.getProperties().Is(IsoFlagType.burntOut)) {
                byte var11 = 0;

                for (int var12 = 0; var12 < this.Objects.size(); var12++) {
                    IsoObject var13 = (IsoObject)this.Objects.get(var12);
                    boolean var6 = false;
                    if (var13.getSprite() == null
                        || var13.getSprite().getName() == null
                        || var13.getSprite().getProperties().Is(IsoFlagType.water)
                        || var13.getSprite().getName().contains("_burnt_")) {
                        continue;
                    }

                    if (var13 instanceof IsoThumpable && var13.getSprite().burntTile != null) {
                        IsoObject var17 = IsoObject.getNew();
                        var17.setSprite(IsoSpriteManager.instance.getSprite(var13.getSprite().burntTile));
                        var17.setSquare(this);
                        if (GameServer.bServer) {
                            var13.sendObjectChange("replaceWith", new Object[]{"object", var17});
                        }

                        var13.removeFromWorld();
                        this.Objects.set(var12, var17);
                    } else if (var13.getSprite().burntTile != null) {
                        var13.sprite = IsoSpriteManager.instance.getSprite(var13.getSprite().burntTile);
                        var13.RemoveAttachedAnims();
                        if (var13.Children != null) {
                            var13.Children.clear();
                        }

                        var13.transmitUpdatedSpriteToClients();
                        var13.setOverlaySprite(null);
                    } else if (var13.getType() == IsoObjectType.tree) {
                        var13.sprite = IsoSpriteManager.instance.getSprite("fencing_burnt_01_" + (Rand.Next(15, 19) + 1));
                        var13.RemoveAttachedAnims();
                        if (var13.Children != null) {
                            var13.Children.clear();
                        }

                        var13.transmitUpdatedSpriteToClients();
                        var13.setOverlaySprite(null);
                    } else {
                        if (var13 instanceof IsoTrap) {
                            continue;
                        }

                        if (!(var13 instanceof IsoBarricade) && !(var13 instanceof IsoMannequin)) {
                            if (var13 instanceof IsoGenerator var16) {
                                if (var16.getFuel() > 0.0F) {
                                    var11 += 20;
                                }

                                if (var16.isActivated()) {
                                    var16.activated = false;
                                    var16.setSurroundingElectricity();
                                    if (GameServer.bServer) {
                                        var16.syncIsoObject(false, (byte)0, null, null);
                                    }
                                }

                                if (GameServer.bServer) {
                                    GameServer.RemoveItemFromMap(var13);
                                } else {
                                    this.RemoveTileObject(var13);
                                }
                            } else if (var13.getType() == IsoObjectType.wall
                                && !var13.getProperties().Is(IsoFlagType.DoorWallW)
                                && !var13.getProperties().Is(IsoFlagType.DoorWallN)
                                && !var13.getProperties().Is("WindowN")
                                && !var13.getProperties().Is(IsoFlagType.WindowW)
                                && !var13.getSprite().getName().startsWith("walls_exterior_roofs_")
                                && !var13.getSprite().getName().startsWith("fencing_")
                                && !var13.getSprite().getName().startsWith("fixtures_railings_")) {
                                if (var13.getSprite().getProperties().Is(IsoFlagType.collideW) && !var13.getSprite().getProperties().Is(IsoFlagType.collideN)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "0" : "4"));
                                } else if (var13.getSprite().getProperties().Is(IsoFlagType.collideN)
                                    && !var13.getSprite().getProperties().Is(IsoFlagType.collideW)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "1" : "5"));
                                } else if (var13.getSprite().getProperties().Is(IsoFlagType.collideW)
                                    && var13.getSprite().getProperties().Is(IsoFlagType.collideN)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "2" : "6"));
                                } else if (var13.getProperties().Is(IsoFlagType.WallSE)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "3" : "7"));
                                }
                            } else {
                                if (var13 instanceof IsoDoor || var13 instanceof IsoWindow || var13 instanceof IsoCurtain) {
                                    if (GameServer.bServer) {
                                        GameServer.RemoveItemFromMap(var13);
                                    } else {
                                        this.RemoveTileObject(var13);
                                        var10 = true;
                                    }
                                }

                                if (var13.getProperties().Is(IsoFlagType.WindowW)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "8" : "12"));
                                } else if (var13.getProperties().Is("WindowN")) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "9" : "13"));
                                } else if (var13.getProperties().Is(IsoFlagType.DoorWallW)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "10" : "14"));
                                } else if (var13.getProperties().Is(IsoFlagType.DoorWallN)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("walls_burnt_01_" + (Rand.Next(2) == 0 ? "11" : "15"));
                                } else if (var13.getSprite().getProperties().Is(IsoFlagType.solidfloor)
                                    && !var13.getSprite().getProperties().Is(IsoFlagType.exterior)) {
                                    var13.sprite = IsoSpriteManager.instance.getSprite("floors_burnt_01_0");
                                } else {
                                    if (var13 instanceof IsoWaveSignal) {
                                        if (GameServer.bServer) {
                                            GameServer.RemoveItemFromMap(var13);
                                        } else {
                                            this.RemoveTileObject(var13);
                                            var10 = true;
                                        }
                                    }

                                    if (var13.getContainer() != null && var13.getContainer().getItems() != null) {
                                        Object var7 = null;

                                        for (int var8 = 0; var8 < var13.getContainer().getItems().size(); var8++) {
                                            var7 = (InventoryItem)var13.getContainer().getItems().get(var8);
                                            if ((!(var7 instanceof Food) || !((Food)var7).isAlcoholic())
                                                && !var7.getType().equals("PetrolCan")
                                                && !var7.getType().equals("Bleach")) {
                                                continue;
                                            }

                                            var11 += 20;
                                            if (var11 > 100) {
                                                var11 = 100;
                                                break;
                                            }
                                        }

                                        var13.sprite = IsoSpriteManager.instance.getSprite("floors_burnt_01_" + Rand.Next(1, 2));

                                        for (int var18 = 0; var18 < var13.getContainerCount(); var18++) {
                                            ItemContainer var9 = var13.getContainerByIndex(var18);
                                            var9.removeItemsFromProcessItems();
                                            var9.removeAllItems();
                                        }

                                        var13.removeAllContainers();
                                        if (var13.getOverlaySprite() != null) {
                                            var13.setOverlaySprite(null);
                                        }

                                        var6 = true;
                                    } else if (!var13.getSprite().getProperties().Is(IsoFlagType.solidtrans)
                                        && !var13.getSprite().getProperties().Is(IsoFlagType.bed)
                                        && !var13.getSprite().getProperties().Is(IsoFlagType.waterPiped)) {
                                        if (var13.getSprite().getName().startsWith("walls_exterior_roofs_")) {
                                            var13.sprite = IsoSpriteManager.instance
                                                .getSprite(
                                                    "walls_burnt_roofs_01_"
                                                        + var13.getSprite()
                                                            .getName()
                                                            .substring(var13.getSprite().getName().lastIndexOf("_") + 1, var13.getSprite().getName().length())
                                                );
                                        } else if (!var13.getSprite().getName().startsWith("roofs_accents")) {
                                            if (var13.getSprite().getName().startsWith("roofs_")) {
                                                var13.sprite = IsoSpriteManager.instance
                                                    .getSprite(
                                                        "roofs_burnt_01_"
                                                            + var13.getSprite()
                                                                .getName()
                                                                .substring(
                                                                    var13.getSprite().getName().lastIndexOf("_") + 1, var13.getSprite().getName().length()
                                                                )
                                                    );
                                            } else {
                                                label419: {
                                                    if (!var13.getSprite().getName().startsWith("fencing_")
                                                            && !var13.getSprite().getName().startsWith("fixtures_railings_")
                                                        || !var13.getSprite().getProperties().Is(IsoFlagType.HoppableN)
                                                            && !var13.getSprite().getProperties().Is(IsoFlagType.HoppableW)) {
                                                        break label419;
                                                    }

                                                    if (var13.getSprite().getProperties().Is(IsoFlagType.transparentW)
                                                        && !var13.getSprite().getProperties().Is(IsoFlagType.transparentN)) {
                                                        var13.sprite = IsoSpriteManager.instance.getSprite("fencing_burnt_01_0");
                                                    } else if (var13.getSprite().getProperties().Is(IsoFlagType.transparentN)
                                                        && !var13.getSprite().getProperties().Is(IsoFlagType.transparentW)) {
                                                        var13.sprite = IsoSpriteManager.instance.getSprite("fencing_burnt_01_1");
                                                    } else {
                                                        var13.sprite = IsoSpriteManager.instance.getSprite("fencing_burnt_01_2");
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        var13.sprite = IsoSpriteManager.instance.getSprite("floors_burnt_01_" + Rand.Next(1, 2));
                                        if (var13.getOverlaySprite() != null) {
                                            var13.setOverlaySprite(null);
                                        }
                                    }
                                }
                            }
                        } else if (GameServer.bServer) {
                            GameServer.RemoveItemFromMap(var13);
                        } else {
                            this.Objects.remove(var13);
                        }
                    }
                }

                if (var11 > 0 && var1) {
                    if (GameServer.bServer) {
                        GameServer.PlayWorldSoundServer("BurnedObjectExploded", false, this, 0.0F, 50.0F, 1.0F, false);
                    } else {
                        SoundManager.instance.PlayWorldSound("BurnedObjectExploded", this, 0.0F, 50.0F, 1.0F, false);
                    }
                }
            }

            if (!var10) {
                this.RecalcProperties();
            }

            this.getProperties().Set(IsoFlagType.burntOut);
            this.burntOut = true;
            MapCollisionData.instance.squareChanged(this);
            PolygonalMap2.instance.squareChanged(this);
        }
    }

    public void BurnWallsTCOnly() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (var2.sprite == null) {
            }
        }
    }

    public void BurnTick() {
        if (!GameClient.bClient) {
            for (int var1 = 0; var1 < this.StaticMovingObjects.size(); var1++) {
                IsoMovingObject var2 = this.StaticMovingObjects.get(var1);
                if (var2 instanceof IsoDeadBody) {
                    ((IsoDeadBody)var2).Burn();
                    if (!this.StaticMovingObjects.contains(var2)) {
                        var1--;
                    }
                }
            }
        }
    }

    public boolean CalculateCollide(IsoGridSquare var1, boolean var2, boolean var3, boolean var4) {
        return this.CalculateCollide(var1, var2, var3, var4, false);
    }

    public boolean CalculateCollide(IsoGridSquare var1, boolean var2, boolean var3, boolean var4, boolean var5) {
        return this.CalculateCollide(var1, var2, var3, var4, var5, cellGetSquare);
    }

    public boolean CalculateCollide(IsoGridSquare var1, boolean var2, boolean var3, boolean var4, boolean var5, GetSquare var6) {
        if (var1 == null && var3) {
            return true;
        } else if (var1 == null) {
            return false;
        } else {
            if (var2 && var1.Properties.Is(IsoFlagType.trans)) {
            }

            boolean var7 = false;
            boolean var8 = false;
            boolean var9 = false;
            boolean var10 = false;
            if (var1.x < this.x) {
                var7 = true;
            }

            if (var1.y < this.y) {
                var9 = true;
            }

            if (var1.x > this.x) {
                var8 = true;
            }

            if (var1.y > this.y) {
                var10 = true;
            }

            if (!var5 && var1.Properties.Is(IsoFlagType.solid)) {
                if (this.Has(IsoObjectType.stairsTW) && !var3 && var1.x < this.x && var1.y == this.y && var1.z == this.z) {
                    return false;
                } else if (this.Has(IsoObjectType.stairsTN) && !var3 && var1.x == this.x && var1.y < this.y && var1.z == this.z) {
                    return false;
                } else {
                    return true;
                }
            } else {
                if (!var4 && var1.Properties.Is(IsoFlagType.solidtrans)) {
                    if (this.Has(IsoObjectType.stairsTW) && !var3 && var1.x < this.x && var1.y == this.y && var1.z == this.z) {
                        return false;
                    }

                    if (this.Has(IsoObjectType.stairsTN) && !var3 && var1.x == this.x && var1.y < this.y && var1.z == this.z) {
                        return false;
                    }

                    boolean var11 = false;
                    if (!var1.Properties.Is(IsoFlagType.windowW) && !var1.Properties.Is(IsoFlagType.windowN)) {
                    }

                    var11 = true;
                }

                if (var1.x != this.x && var1.y != this.y && this.z != var1.z && var3) {
                    return true;
                } else if (var3 && var1.z < this.z && (this.SolidFloorCached ? !this.SolidFloor : !this.TreatAsSolidFloor())) {
                    if (!var1.Has(IsoObjectType.stairsTN) && !var1.Has(IsoObjectType.stairsTW)) {
                        return false;
                    } else {
                        return true;
                    }
                } else {
                    if (var3 && var1.z == this.z) {
                        if (var1.x > this.x && var1.y == this.y && var1.Properties.Is(IsoFlagType.windowW)) {
                            return false;
                        }

                        if (var1.y > this.y && var1.x == this.x && var1.Properties.Is(IsoFlagType.windowN)) {
                            return false;
                        }

                        if (var1.x < this.x && var1.y == this.y && this.Properties.Is(IsoFlagType.windowW)) {
                            return false;
                        }

                        if (var1.y < this.y && var1.x == this.x && this.Properties.Is(IsoFlagType.windowN)) {
                            return false;
                        }
                    }

                    if (var1.x > this.x && var1.z < this.z && var1.Has(IsoObjectType.stairsTW)) {
                        return false;
                    } else if (var1.y > this.y && var1.z < this.z && var1.Has(IsoObjectType.stairsTN)) {
                        return false;
                    } else {
                        IsoGridSquare var19 = var6.getGridSquare(var1.x, var1.y, var1.z - 1);
                        if (var1.x != this.x
                            && var1.z == this.z
                            && var1.Has(IsoObjectType.stairsTN)
                            && (var19 == null || !var19.Has(IsoObjectType.stairsTN) || var3)) {
                            return true;
                        } else if (var1.y > this.y
                            && var1.x == this.x
                            && var1.z == this.z
                            && var1.Has(IsoObjectType.stairsTN)
                            && (var19 == null || !var19.Has(IsoObjectType.stairsTN) || var3)) {
                            return true;
                        } else if (var1.x > this.x
                            && var1.y == this.y
                            && var1.z == this.z
                            && var1.Has(IsoObjectType.stairsTW)
                            && (var19 == null || !var19.Has(IsoObjectType.stairsTW) || var3)) {
                            return true;
                        } else if (var1.y != this.y
                            && var1.z == this.z
                            && var1.Has(IsoObjectType.stairsTW)
                            && (var19 == null || !var19.Has(IsoObjectType.stairsTW) || var3)) {
                            return true;
                        } else if (var1.x != this.x && var1.z == this.z && var1.Has(IsoObjectType.stairsMN)) {
                            return true;
                        } else if (var1.y != this.y && var1.z == this.z && var1.Has(IsoObjectType.stairsMW)) {
                            return true;
                        } else if (var1.x != this.x && var1.z == this.z && var1.Has(IsoObjectType.stairsBN)) {
                            return true;
                        } else if (var1.y != this.y && var1.z == this.z && var1.Has(IsoObjectType.stairsBW)) {
                            return true;
                        } else if (var1.x != this.x && var1.z == this.z && this.Has(IsoObjectType.stairsTN)) {
                            return true;
                        } else if (var1.y != this.y && var1.z == this.z && this.Has(IsoObjectType.stairsTW)) {
                            return true;
                        } else if (var1.x != this.x && var1.z == this.z && this.Has(IsoObjectType.stairsMN)) {
                            return true;
                        } else if (var1.y != this.y && var1.z == this.z && this.Has(IsoObjectType.stairsMW)) {
                            return true;
                        } else if (var1.x != this.x && var1.z == this.z && this.Has(IsoObjectType.stairsBN)) {
                            return true;
                        } else if (var1.y != this.y && var1.z == this.z && this.Has(IsoObjectType.stairsBW)) {
                            return true;
                        } else if (var1.y < this.y && var1.x == this.x && var1.z > this.z && this.Has(IsoObjectType.stairsTN)) {
                            return false;
                        } else if (var1.x < this.x && var1.y == this.y && var1.z > this.z && this.Has(IsoObjectType.stairsTW)) {
                            return false;
                        } else if (var1.y > this.y && var1.x == this.x && var1.z < this.z && var1.Has(IsoObjectType.stairsTN)) {
                            return false;
                        } else if (var1.x > this.x && var1.y == this.y && var1.z < this.z && var1.Has(IsoObjectType.stairsTW)) {
                            return false;
                        } else if (var1.z == this.z && (var1.SolidFloorCached ? !var1.SolidFloor : !var1.TreatAsSolidFloor()) && var3) {
                            return true;
                        } else {
                            if (var1.z == this.z && (var1.SolidFloorCached ? !var1.SolidFloor : !var1.TreatAsSolidFloor()) && var1.z > 0) {
                                var19 = var6.getGridSquare(var1.x, var1.y, var1.z - 1);
                                if (var19 == null) {
                                    return true;
                                }
                            }

                            if (this.z != var1.z) {
                                if (var1.z < this.z
                                    && var1.x == this.x
                                    && var1.y == this.y
                                    && (this.SolidFloorCached ? !this.SolidFloor : !this.TreatAsSolidFloor())) {
                                    return false;
                                } else {
                                    return true;
                                }
                            } else {
                                boolean var22 = var9 && this.Properties.Is(IsoFlagType.collideN);
                                boolean var13 = var7 && this.Properties.Is(IsoFlagType.collideW);
                                boolean var14 = var10 && var1.Properties.Is(IsoFlagType.collideN);
                                boolean var15 = var8 && var1.Properties.Is(IsoFlagType.collideW);
                                if (var22 && var3 && this.Properties.Is(IsoFlagType.canPathN)) {
                                    var22 = false;
                                }

                                if (var13 && var3 && this.Properties.Is(IsoFlagType.canPathW)) {
                                    var13 = false;
                                }

                                if (var14 && var3 && var1.Properties.Is(IsoFlagType.canPathN)) {
                                    var14 = false;
                                }

                                if (var15 && var3 && var1.Properties.Is(IsoFlagType.canPathW)) {
                                    var15 = false;
                                }

                                if (var13 && this.Has(IsoObjectType.stairsTW) && !var3) {
                                    var13 = false;
                                }

                                if (var22 && this.Has(IsoObjectType.stairsTN) && !var3) {
                                    var22 = false;
                                }

                                if (!var22 && !var13 && !var14 && !var15) {
                                    boolean var16 = var1.x != this.x && var1.y != this.y;
                                    if (var16) {
                                        IsoGridSquare var17 = var6.getGridSquare(this.x, var1.y, this.z);
                                        IsoGridSquare var18 = var6.getGridSquare(var1.x, this.y, this.z);
                                        if (var17 != null && var17 != this && var17 != var1) {
                                            var17.RecalcPropertiesIfNeeded();
                                        }

                                        if (var18 != null && var18 != this && var18 != var1) {
                                            var18.RecalcPropertiesIfNeeded();
                                        }

                                        if (var1 == this || var17 == var18 || var17 == this || var18 == this || var17 == var1 || var18 == var1) {
                                            return true;
                                        }

                                        if (var1.x == this.x + 1
                                            && var1.y == this.y + 1
                                            && var17 != null
                                            && var18 != null
                                            && var17.Is(IsoFlagType.windowN)
                                            && var18.Is(IsoFlagType.windowW)) {
                                            return true;
                                        }

                                        if (var1.x == this.x - 1
                                            && var1.y == this.y - 1
                                            && var17 != null
                                            && var18 != null
                                            && var17.Is(IsoFlagType.windowW)
                                            && var18.Is(IsoFlagType.windowN)) {
                                            return true;
                                        }

                                        if (this.CalculateCollide(var17, var2, var3, var4, false, var6)) {
                                            return true;
                                        }

                                        if (this.CalculateCollide(var18, var2, var3, var4, false, var6)) {
                                            return true;
                                        }

                                        if (var1.CalculateCollide(var17, var2, var3, var4, false, var6)) {
                                            return true;
                                        }

                                        if (var1.CalculateCollide(var18, var2, var3, var4, false, var6)) {
                                            return true;
                                        }
                                    }

                                    return false;
                                } else {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    public boolean CalculateVisionBlocked(IsoGridSquare var1) {
        return this.CalculateVisionBlocked(var1, cellGetSquare);
    }

    public boolean CalculateVisionBlocked(IsoGridSquare var1, GetSquare var2) {
        if (var1 == null) {
            return false;
        } else if (Math.abs(var1.getX() - this.getX()) <= 1 && Math.abs(var1.getY() - this.getY()) <= 1) {
            boolean var3 = false;
            boolean var4 = false;
            boolean var5 = false;
            boolean var6 = false;
            if (var1.x < this.x) {
                var3 = true;
            }

            if (var1.y < this.y) {
                var5 = true;
            }

            if (var1.x > this.x) {
                var4 = true;
            }

            if (var1.y > this.y) {
                var6 = true;
            }

            if (!var1.Properties.Is(IsoFlagType.trans) && !this.Properties.Is(IsoFlagType.trans)) {
                if (this.z != var1.z) {
                    if (var1.z > this.z) {
                        if ((var1.SolidFloorCached ? var1.SolidFloor : var1.TreatAsSolidFloor()) && !var1.getProperties().Is(IsoFlagType.transparentFloor)) {
                            return true;
                        }

                        if (this.Properties.Is(IsoFlagType.noStart)) {
                            return true;
                        }

                        IsoGridSquare var7 = var2.getGridSquare(this.x, this.y, var1.z);
                        if (var7 == null) {
                            return false;
                        }

                        if ((var7.SolidFloorCached ? var7.SolidFloor : var7.TreatAsSolidFloor()) && !var7.getProperties().Is(IsoFlagType.transparentFloor)) {
                            return true;
                        }
                    } else {
                        if ((this.SolidFloorCached ? this.SolidFloor : this.TreatAsSolidFloor()) && !this.getProperties().Is(IsoFlagType.transparentFloor)) {
                            return true;
                        }

                        if (this.Properties.Is(IsoFlagType.noStart)) {
                            return true;
                        }

                        IsoGridSquare var14 = var2.getGridSquare(var1.x, var1.y, this.z);
                        if (var14 == null) {
                            return false;
                        }

                        if ((var14.SolidFloorCached ? var14.SolidFloor : var14.TreatAsSolidFloor()) && !var14.getProperties().Is(IsoFlagType.transparentFloor)) {
                            return true;
                        }
                    }
                }

                if (var1.x > this.x && var1.Properties.Is(IsoFlagType.transparentW)) {
                    return false;
                } else if (var1.y > this.y && var1.Properties.Is(IsoFlagType.transparentN)) {
                    return false;
                } else if (var1.x < this.x && this.Properties.Is(IsoFlagType.transparentW)) {
                    return false;
                } else if (var1.y < this.y && this.Properties.Is(IsoFlagType.transparentN)) {
                    return false;
                } else if (var1.x > this.x && var1.Properties.Is(IsoFlagType.doorW)) {
                    return false;
                } else if (var1.y > this.y && var1.Properties.Is(IsoFlagType.doorN)) {
                    return false;
                } else if (var1.x < this.x && this.Properties.Is(IsoFlagType.doorW)) {
                    return false;
                } else if (var1.y < this.y && this.Properties.Is(IsoFlagType.doorN)) {
                    return false;
                } else {
                    boolean var15 = var5 && this.Properties.Is(IsoFlagType.collideN);
                    boolean var8 = var3 && this.Properties.Is(IsoFlagType.collideW);
                    boolean var9 = var6 && var1.Properties.Is(IsoFlagType.collideN);
                    boolean var10 = var4 && var1.Properties.Is(IsoFlagType.collideW);
                    if (!var15 && !var8 && !var9 && !var10) {
                        boolean var11 = var1.x != this.x && var1.y != this.y;
                        if (!var1.Properties.Is(IsoFlagType.solid) && !var1.Properties.Is(IsoFlagType.blocksight)) {
                            if (var11) {
                                IsoGridSquare var12 = var2.getGridSquare(this.x, var1.y, this.z);
                                IsoGridSquare var13 = var2.getGridSquare(var1.x, this.y, this.z);
                                if (var12 != null && var12 != this && var12 != var1) {
                                    var12.RecalcPropertiesIfNeeded();
                                }

                                if (var13 != null && var13 != this && var13 != var1) {
                                    var13.RecalcPropertiesIfNeeded();
                                }

                                if (this.CalculateVisionBlocked(var12)) {
                                    return true;
                                }

                                if (this.CalculateVisionBlocked(var13)) {
                                    return true;
                                }

                                if (var1.CalculateVisionBlocked(var12)) {
                                    return true;
                                }

                                if (var1.CalculateVisionBlocked(var13)) {
                                    return true;
                                }
                            }

                            return false;
                        } else {
                            return true;
                        }
                    } else {
                        return true;
                    }
                }
            } else {
                return false;
            }
        } else {
            return true;
        }
    }

    public IsoGameCharacter FindFriend(IsoGameCharacter var1, int var2, Stack<IsoGameCharacter> var3) {
        Stack var4 = new Stack();

        for (int var5 = 0; var5 < var1.getLocalList().size(); var5++) {
            IsoMovingObject var6 = (IsoMovingObject)var1.getLocalList().get(var5);
            if (var6 != var1 && var6 != var1.getFollowingTarget() && var6 instanceof IsoGameCharacter && !(var6 instanceof IsoZombie) && !var3.contains(var6)) {
                var4.add((IsoGameCharacter)var6);
            }
        }

        float var10 = 1000000.0F;
        IsoGameCharacter var11 = null;

        for (IsoGameCharacter var8 : var4) {
            float var9 = 0.0F;
            var9 = var9 + Math.abs((float)this.getX() - var8.getX());
            var9 = var9 + Math.abs((float)this.getY() - var8.getY());
            var9 = var9 + Math.abs((float)this.getZ() - var8.getZ());
            if (var9 < var10) {
                var11 = var8;
                var10 = var9;
            }

            if (var8 == IsoPlayer.getInstance()) {
                var11 = var8;
                var9 = 0.0F;
            }
        }

        if (var10 > (float)var2) {
            return null;
        } else {
            return var11;
        }
    }

    public IsoGameCharacter FindEnemy(IsoGameCharacter var1, int var2, ArrayList<IsoMovingObject> var3, IsoGameCharacter var4, int var5) {
        float var6 = 1000000.0F;
        IsoGameCharacter var7 = null;

        for (int var8 = 0; var8 < var3.size(); var8++) {
            IsoGameCharacter var9 = (IsoGameCharacter)var3.get(var8);
            float var10 = 0.0F;
            var10 = var10 + Math.abs((float)this.getX() - var9.getX());
            var10 = var10 + Math.abs((float)this.getY() - var9.getY());
            var10 = var10 + Math.abs((float)this.getZ() - var9.getZ());
            if (var10 < (float)var2 && var10 < var6 && var9.DistTo(var4) < (float)var5) {
                var7 = var9;
                var6 = var10;
            }
        }

        if (var6 > (float)var2) {
            return null;
        } else {
            return var7;
        }
    }

    public IsoGameCharacter FindEnemy(IsoGameCharacter var1, int var2, ArrayList<IsoMovingObject> var3) {
        float var4 = 1000000.0F;
        IsoGameCharacter var5 = null;

        for (int var6 = 0; var6 < var3.size(); var6++) {
            IsoGameCharacter var7 = (IsoGameCharacter)var3.get(var6);
            float var8 = 0.0F;
            var8 = var8 + Math.abs((float)this.getX() - var7.getX());
            var8 = var8 + Math.abs((float)this.getY() - var7.getY());
            var8 = var8 + Math.abs((float)this.getZ() - var7.getZ());
            if (var8 < var4) {
                var5 = var7;
                var4 = var8;
            }
        }

        if (var4 > (float)var2) {
            return null;
        } else {
            return var5;
        }
    }

    public int getX() {
        return this.x;
    }

    public int getY() {
        return this.y;
    }

    public int getZ() {
        return this.z;
    }

    public void RecalcProperties() {
        this.CachedIsFree = false;
        String var1 = null;
        if (this.Properties.Is("waterAmount")) {
            var1 = this.Properties.Val("waterAmount");
        }

        String var2 = null;
        if (this.Properties.Is("fuelAmount")) {
            var2 = this.Properties.Val("fuelAmount");
        }

        if (this.zone == null) {
            this.zone = IsoWorld.instance.MetaGrid.getZoneAt(this.x, this.y, this.z);
        }

        this.Properties.Clear();
        this.hasTypes.clear();
        this.hasTree = false;
        boolean var3 = false;
        boolean var4 = false;
        boolean var5 = false;
        boolean var6 = false;
        boolean var7 = false;
        boolean var8 = false;
        boolean var9 = false;
        boolean var10 = false;
        int var11 = this.Objects.size();
        IsoObject[] var12 = (IsoObject[])this.Objects.getElements();

        for (int var13 = 0; var13 < var11; var13++) {
            IsoObject var14 = var12[var13];
            if (var14 != null) {
                PropertyContainer var15 = var14.getProperties();
                if (var15 != null && !var15.Is(IsoFlagType.blueprint)) {
                    if (var14.sprite.forceRender) {
                        var10 = true;
                    }

                    if (var14.getType() == IsoObjectType.tree) {
                        this.hasTree = true;
                    }

                    this.hasTypes.set(var14.getType(), true);
                    this.Properties.AddProperties(var15);
                    if (var15.Is(IsoFlagType.water)) {
                        var4 = false;
                    } else {
                        if (!var4 && var15.Is(IsoFlagType.solidfloor)) {
                            var4 = true;
                        }

                        if (!var3 && var15.Is(IsoFlagType.solidtrans)) {
                            var3 = true;
                        }

                        if (!var5 && var15.Is(IsoFlagType.solidfloor) && !var15.Is(IsoFlagType.transparentFloor)) {
                            var5 = true;
                        }
                    }
                }
            }
        }

        if (this.roomID == -1 && !this.haveRoof) {
            this.getProperties().Set(IsoFlagType.exterior);

            try {
                this.getPuddles().bRecalc = true;
            } catch (Exception var16) {
                var16.printStackTrace();
            }
        } else {
            this.getProperties().UnSet(IsoFlagType.exterior);

            try {
                this.getPuddles().bRecalc = true;
            } catch (Exception var17) {
                var17.printStackTrace();
            }
        }
    }

    public void RecalcPropertiesIfNeeded() {
        if (this.propertiesDirty) {
            this.RecalcProperties();
        }
    }

    public void ReCalculateCollide(IsoGridSquare var1) {
        this.ReCalculateCollide(var1, cellGetSquare);
    }

    public void ReCalculateCollide(IsoGridSquare var1, GetSquare var2) {
        if (1 + (var1.x - this.x) >= 0 && 1 + (var1.y - this.y) >= 0 && 1 + (var1.z - this.z) >= 0) {
        }

        DebugLog.log("ERROR");
    }

    public void ReCalculatePathFind(IsoGridSquare var1) {
        this.ReCalculatePathFind(var1, cellGetSquare);
    }

    public void ReCalculatePathFind(IsoGridSquare var1, GetSquare var2) {
        boolean var3 = this.CalculateCollide(var1, false, true, false, false, var2);
        this.pathMatrix = setMatrixBit(this.pathMatrix, 1 + (var1.x - this.x), 1 + (var1.y - this.y), 1 + (var1.z - this.z), var3);
    }

    public void ReCalculateVisionBlocked(IsoGridSquare var1) {
        this.ReCalculateVisionBlocked(var1, cellGetSquare);
    }

    public void ReCalculateVisionBlocked(IsoGridSquare var1, GetSquare var2) {
        boolean var3 = this.CalculateVisionBlocked(var1, var2);
        this.visionMatrix = setMatrixBit(this.visionMatrix, 1 + (var1.x - this.x), 1 + (var1.y - this.y), 1 + (var1.z - this.z), var3);
    }

    private static boolean testCollideSpecialObjects(IsoMovingObject var0, IsoGridSquare var1, IsoGridSquare var2) {
        for (int var3 = 0; var3 < var2.SpecialObjects.size(); var3++) {
            IsoObject var4 = var2.SpecialObjects.get(var3);
            if (var4.TestCollide(var0, var1, var2)) {
                if (var4 instanceof IsoDoor) {
                    var0.setCollidedWithDoor(true);
                } else if (var4 instanceof IsoThumpable && ((IsoThumpable)var4).isDoor) {
                    var0.setCollidedWithDoor(true);
                }
            }
        }

        return false;
    }

    public boolean testCollideAdjacent(IsoMovingObject var1, int var2, int var3, int var4) {
        if (var1 instanceof IsoPlayer && ((IsoPlayer)var1).isNoClip()) {
            return false;
        } else if (this.collideMatrix == -1) {
            return true;
        } else if (var2 >= -1 && var2 <= 1 && var3 >= -1 && var3 <= 1 && var4 >= -1 && var4 <= 1) {
            if (this.x + var2 >= 0 && this.y + var3 >= 0 && IsoWorld.instance.MetaGrid.isValidChunk((this.x + var2) / 10, (this.y + var3) / 10)) {
                IsoGridSquare var5 = this.getCell().getGridSquare(this.x + var2, this.y + var3, this.z + var4);
                SafeHouse var6 = null;
                if ((GameServer.bServer || GameClient.bClient) && var1 instanceof IsoPlayer && !ServerOptions.instance.SafehouseAllowTrepass.getValue()) {
                    IsoGridSquare var7 = this.getCell().getGridSquare(this.x + var2, this.y + var3, 0);
                    var6 = SafeHouse.isSafeHouse(var7, ((IsoPlayer)var1).getUsername(), true);
                }

                if (var6 != null) {
                    return true;
                } else {
                    if (var5 != null && var1 != null) {
                        IsoObject var8 = this.testCollideSpecialObjects(var5);
                        if (var8 != null) {
                            var1.collideWith(var8);
                            if (var8 instanceof IsoDoor) {
                                var1.setCollidedWithDoor(true);
                            } else if (var8 instanceof IsoThumpable && ((IsoThumpable)var8).isDoor) {
                                var1.setCollidedWithDoor(true);
                            }
                        }
                    }

                    if (UseSlowCollision) {
                        return this.CalculateCollide(var5, false, false, false);
                    } else {
                        if (var1 instanceof IsoPlayer && getMatrixBit(this.collideMatrix, var2 + 1, var3 + 1, var4 + 1)) {
                            this.RecalcAllWithNeighbours(true);
                        }

                        return getMatrixBit(this.collideMatrix, var2 + 1, var3 + 1, var4 + 1);
                    }
                }
            } else {
                return true;
            }
        } else {
            return true;
        }
    }

    public boolean testCollideAdjacentAdvanced(int var1, int var2, int var3, boolean var4) {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:45
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:310)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 00: aload 0
        // 01: getfield zombie/iso/IsoGridSquare.collideMatrix I
        // 04: bipush -1
        // 05: if_icmpne 0a
        // 08: bipush 1
        // 09: ireturn
        // 0a: iload 1
        // 0b: bipush -1
        // 0c: if_icmplt 28
        // 0f: iload 1
        // 10: bipush 1
        // 11: if_icmpgt 28
        // 14: iload 2
        // 15: bipush -1
        // 16: if_icmplt 28
        // 19: iload 2
        // 1a: bipush 1
        // 1b: if_icmpgt 28
        // 1e: iload 3
        // 1f: bipush -1
        // 20: if_icmplt 28
        // 23: iload 3
        // 24: bipush 1
        // 25: if_icmple 2a
        // 28: bipush 1
        // 29: ireturn
        // 2a: aload 0
        // 2b: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 2e: aload 0
        // 2f: getfield zombie/iso/IsoGridSquare.x I
        // 32: iload 1
        // 33: iadd
        // 34: aload 0
        // 35: getfield zombie/iso/IsoGridSquare.y I
        // 38: iload 2
        // 39: iadd
        // 3a: aload 0
        // 3b: getfield zombie/iso/IsoGridSquare.z I
        // 3e: iload 3
        // 3f: iadd
        // 40: invokevirtual zombie/iso/IsoCell.getGridSquare (III)Lzombie/iso/IsoGridSquare;
        // 43: astore 5
        // 45: aload 5
        // 47: ifnull c3
        // 4a: aload 5
        // 4c: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 4f: invokevirtual java/util/ArrayList.isEmpty ()Z
        // 52: ifne 88
        // 55: bipush 0
        // 56: istore 6
        // 58: iload 6
        // 5a: aload 5
        // 5c: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 5f: invokevirtual java/util/ArrayList.size ()I
        // 62: if_icmpge 88
        // 65: aload 5
        // 67: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 6a: iload 6
        // 6c: invokevirtual java/util/ArrayList.get (I)Ljava/lang/Object;
        // 6f: checkcast zombie/iso/IsoObject
        // 72: astore 7
        // 74: aload 7
        // 76: aconst_null
        // 77: aload 0
        // 78: aload 5
        // 7a: invokevirtual zombie/iso/IsoObject.TestCollide (Lzombie/iso/IsoMovingObject;Lzombie/iso/IsoGridSquare;Lzombie/iso/IsoGridSquare;)Z
        // 7d: ifeq 82
        // 80: bipush 1
        // 81: ireturn
        // 82: iinc 6 1
        // 85: goto 58
        // 88: aload 0
        // 89: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 8c: invokevirtual java/util/ArrayList.isEmpty ()Z
        // 8f: ifne c3
        // 92: bipush 0
        // 93: istore 6
        // 95: iload 6
        // 97: aload 0
        // 98: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 9b: invokevirtual java/util/ArrayList.size ()I
        // 9e: if_icmpge c3
        // a1: aload 0
        // a2: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // a5: iload 6
        // a7: invokevirtual java/util/ArrayList.get (I)Ljava/lang/Object;
        // aa: checkcast zombie/iso/IsoObject
        // ad: astore 7
        // af: aload 7
        // b1: aconst_null
        // b2: aload 0
        // b3: aload 5
        // b5: invokevirtual zombie/iso/IsoObject.TestCollide (Lzombie/iso/IsoMovingObject;Lzombie/iso/IsoGridSquare;Lzombie/iso/IsoGridSquare;)Z
        // b8: ifeq bd
        // bb: bipush 1
        // bc: ireturn
        // bd: iinc 6 1
        // c0: goto 95
        // c3: getstatic zombie/iso/IsoGridSquare.UseSlowCollision Z
        // c6: ifeq d3
        // c9: aload 0
        // ca: aload 5
        // cc: bipush 0
        // cd: bipush 0
        // ce: bipush 0
        // cf: invokevirtual zombie/iso/IsoGridSquare.CalculateCollide (Lzombie/iso/IsoGridSquare;ZZZ)Z
        // d2: ireturn
        // d3: aload 0
        // d4: getfield zombie/iso/IsoGridSquare.collideMatrix I
        // d7: iload 1
        // d8: bipush 1
        // d9: iadd
        // da: iload 2
        // db: bipush 1
        // dc: iadd
        // dd: iload 3
        // de: bipush 1
        // df: iadd
        // e0: invokestatic zombie/iso/IsoGridSquare.getMatrixBit (IIII)Z
        // e3: ireturn
        return false;
    }

    public static void setCollisionMode() {
        UseSlowCollision = !UseSlowCollision;
    }

    public boolean testPathFindAdjacent(IsoMovingObject var1, int var2, int var3, int var4) {
        return this.testPathFindAdjacent(var1, var2, var3, var4, cellGetSquare);
    }

    public boolean testPathFindAdjacent(IsoMovingObject var1, int var2, int var3, int var4, GetSquare var5) {
        if (var2 >= -1 && var2 <= 1 && var3 >= -1 && var3 <= 1 && var4 >= -1 && var4 <= 1) {
            if (!this.Has(IsoObjectType.stairsTN) && !this.Has(IsoObjectType.stairsTW)) {
            }

            IsoGridSquare var6 = var5.getGridSquare(var2 + this.x, var3 + this.y, var4 + this.z);
            if (var6 == null) {
                return true;
            }

            if (this.Has(IsoObjectType.stairsTN) && var6.y < this.y && var6.z == this.z) {
                return true;
            }

            if (this.Has(IsoObjectType.stairsTW) && var6.x < this.x && var6.z == this.z) {
                return true;
            }
        } else {
            return true;
        }

        return false;
    }

    public TestResults testVisionAdjacent(int var1, int var2, int var3, boolean var4, boolean var5) {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:232
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:310)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 000: iload 1
        // 001: bipush -1
        // 002: if_icmplt 01e
        // 005: iload 1
        // 006: bipush 1
        // 007: if_icmpgt 01e
        // 00a: iload 2
        // 00b: bipush -1
        // 00c: if_icmplt 01e
        // 00f: iload 2
        // 010: bipush 1
        // 011: if_icmpgt 01e
        // 014: iload 3
        // 015: bipush -1
        // 016: if_icmplt 01e
        // 019: iload 3
        // 01a: bipush 1
        // 01b: if_icmple 022
        // 01e: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 021: areturn
        // 022: iload 3
        // 023: bipush 1
        // 024: if_icmpne 05f
        // 027: iload 1
        // 028: ifne 02f
        // 02b: iload 2
        // 02c: ifeq 05f
        // 02f: aload 0
        // 030: invokevirtual zombie/iso/IsoGridSquare.HasElevatedFloor ()Z
        // 033: ifeq 05f
        // 036: aload 0
        // 037: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 03a: aload 0
        // 03b: getfield zombie/iso/IsoGridSquare.x I
        // 03e: aload 0
        // 03f: getfield zombie/iso/IsoGridSquare.y I
        // 042: aload 0
        // 043: getfield zombie/iso/IsoGridSquare.z I
        // 046: iload 3
        // 047: iadd
        // 048: invokevirtual zombie/iso/IsoCell.getGridSquare (III)Lzombie/iso/IsoGridSquare;
        // 04b: astore 6
        // 04d: aload 6
        // 04f: ifnull 05f
        // 052: aload 6
        // 054: iload 1
        // 055: iload 2
        // 056: bipush 0
        // 057: iload 4
        // 059: iload 5
        // 05b: invokevirtual zombie/iso/IsoGridSquare.testVisionAdjacent (IIIZZ)Lzombie/iso/LosUtil$TestResults;
        // 05e: areturn
        // 05f: iload 3
        // 060: bipush -1
        // 061: if_icmpne 0a0
        // 064: iload 1
        // 065: ifne 06c
        // 068: iload 2
        // 069: ifeq 0a0
        // 06c: aload 0
        // 06d: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 070: aload 0
        // 071: getfield zombie/iso/IsoGridSquare.x I
        // 074: iload 1
        // 075: iadd
        // 076: aload 0
        // 077: getfield zombie/iso/IsoGridSquare.y I
        // 07a: iload 2
        // 07b: iadd
        // 07c: aload 0
        // 07d: getfield zombie/iso/IsoGridSquare.z I
        // 080: iload 3
        // 081: iadd
        // 082: invokevirtual zombie/iso/IsoCell.getGridSquare (III)Lzombie/iso/IsoGridSquare;
        // 085: astore 6
        // 087: aload 6
        // 089: ifnull 0a0
        // 08c: aload 6
        // 08e: invokevirtual zombie/iso/IsoGridSquare.HasElevatedFloor ()Z
        // 091: ifeq 0a0
        // 094: aload 0
        // 095: iload 1
        // 096: iload 2
        // 097: bipush 0
        // 098: iload 4
        // 09a: iload 5
        // 09c: invokevirtual zombie/iso/IsoGridSquare.testVisionAdjacent (IIIZZ)Lzombie/iso/LosUtil$TestResults;
        // 09f: areturn
        // 0a0: getstatic zombie/iso/LosUtil$TestResults.Clear Lzombie/iso/LosUtil$TestResults;
        // 0a3: astore 6
        // 0a5: iload 1
        // 0a6: ifeq 10f
        // 0a9: iload 2
        // 0aa: ifeq 10f
        // 0ad: iload 4
        // 0af: ifeq 10f
        // 0b2: aload 0
        // 0b3: iload 1
        // 0b4: iload 2
        // 0b5: iload 3
        // 0b6: iload 5
        // 0b8: invokevirtual zombie/iso/IsoGridSquare.DoDiagnalCheck (IIIZ)Lzombie/iso/LosUtil$TestResults;
        // 0bb: astore 6
        // 0bd: aload 6
        // 0bf: getstatic zombie/iso/LosUtil$TestResults.Clear Lzombie/iso/LosUtil$TestResults;
        // 0c2: if_acmpeq 0dd
        // 0c5: aload 6
        // 0c7: getstatic zombie/iso/LosUtil$TestResults.ClearThroughWindow Lzombie/iso/LosUtil$TestResults;
        // 0ca: if_acmpeq 0dd
        // 0cd: aload 6
        // 0cf: getstatic zombie/iso/LosUtil$TestResults.ClearThroughOpenDoor Lzombie/iso/LosUtil$TestResults;
        // 0d2: if_acmpeq 0dd
        // 0d5: aload 6
        // 0d7: getstatic zombie/iso/LosUtil$TestResults.ClearThroughClosedDoor Lzombie/iso/LosUtil$TestResults;
        // 0da: if_acmpne 3f7
        // 0dd: aload 0
        // 0de: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 0e1: aload 0
        // 0e2: getfield zombie/iso/IsoGridSquare.x I
        // 0e5: iload 1
        // 0e6: iadd
        // 0e7: aload 0
        // 0e8: getfield zombie/iso/IsoGridSquare.y I
        // 0eb: iload 2
        // 0ec: iadd
        // 0ed: aload 0
        // 0ee: getfield zombie/iso/IsoGridSquare.z I
        // 0f1: iload 3
        // 0f2: iadd
        // 0f3: invokevirtual zombie/iso/IsoCell.getGridSquare (III)Lzombie/iso/IsoGridSquare;
        // 0f6: astore 7
        // 0f8: aload 7
        // 0fa: ifnull 10c
        // 0fd: aload 7
        // 0ff: iload 1
        // 100: ineg
        // 101: iload 2
        // 102: ineg
        // 103: iload 3
        // 104: ineg
        // 105: iload 5
        // 107: invokevirtual zombie/iso/IsoGridSquare.DoDiagnalCheck (IIIZ)Lzombie/iso/LosUtil$TestResults;
        // 10a: astore 6
        // 10c: goto 3f7
        // 10f: aload 0
        // 110: invokevirtual zombie/iso/IsoGridSquare.getCell ()Lzombie/iso/IsoCell;
        // 113: aload 0
        // 114: getfield zombie/iso/IsoGridSquare.x I
        // 117: iload 1
        // 118: iadd
        // 119: aload 0
        // 11a: getfield zombie/iso/IsoGridSquare.y I
        // 11d: iload 2
        // 11e: iadd
        // 11f: aload 0
        // 120: getfield zombie/iso/IsoGridSquare.z I
        // 123: iload 3
        // 124: iadd
        // 125: invokevirtual zombie/iso/IsoCell.getGridSquare (III)Lzombie/iso/IsoGridSquare;
        // 128: astore 7
        // 12a: getstatic zombie/iso/LosUtil$TestResults.Clear Lzombie/iso/LosUtil$TestResults;
        // 12d: astore 8
        // 12f: aload 7
        // 131: ifnull 3d7
        // 134: aload 7
        // 136: getfield zombie/iso/IsoGridSquare.z I
        // 139: aload 0
        // 13a: getfield zombie/iso/IsoGridSquare.z I
        // 13d: if_icmpne 3d7
        // 140: aload 0
        // 141: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 144: invokevirtual java/util/ArrayList.isEmpty ()Z
        // 147: ifne 28a
        // 14a: bipush 0
        // 14b: istore 9
        // 14d: iload 9
        // 14f: aload 0
        // 150: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 153: invokevirtual java/util/ArrayList.size ()I
        // 156: if_icmpge 28a
        // 159: aload 0
        // 15a: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 15d: iload 9
        // 15f: invokevirtual java/util/ArrayList.get (I)Ljava/lang/Object;
        // 162: checkcast zombie/iso/IsoObject
        // 165: astore 10
        // 167: aload 10
        // 169: ifnonnull 170
        // 16c: getstatic zombie/iso/LosUtil$TestResults.Clear Lzombie/iso/LosUtil$TestResults;
        // 16f: areturn
        // 170: aload 10
        // 172: aload 0
        // 173: aload 7
        // 175: invokevirtual zombie/iso/IsoObject.TestVision (Lzombie/iso/IsoGridSquare;Lzombie/iso/IsoGridSquare;)Lzombie/iso/IsoObject$VisionResult;
        // 178: astore 11
        // 17a: aload 11
        // 17c: getstatic zombie/iso/IsoObject$VisionResult.NoEffect Lzombie/iso/IsoObject$VisionResult;
        // 17f: if_acmpeq 284
        // 182: aload 11
        // 184: getstatic zombie/iso/IsoObject$VisionResult.Unblocked Lzombie/iso/IsoObject$VisionResult;
        // 187: if_acmpne 1ab
        // 18a: aload 10
        // 18c: instanceof zombie/iso/objects/IsoDoor
        // 18f: ifeq 1ab
        // 192: aload 10
        // 194: checkcast zombie/iso/objects/IsoDoor
        // 197: invokevirtual zombie/iso/objects/IsoDoor.IsOpen ()Z
        // 19a: ifeq 1a3
        // 19d: getstatic zombie/iso/LosUtil$TestResults.ClearThroughOpenDoor Lzombie/iso/LosUtil$TestResults;
        // 1a0: goto 1a6
        // 1a3: getstatic zombie/iso/LosUtil$TestResults.ClearThroughClosedDoor Lzombie/iso/LosUtil$TestResults;
        // 1a6: astore 8
        // 1a8: goto 284
        // 1ab: aload 11
        // 1ad: getstatic zombie/iso/IsoObject$VisionResult.Unblocked Lzombie/iso/IsoObject$VisionResult;
        // 1b0: if_acmpne 1d1
        // 1b3: aload 10
        // 1b5: instanceof zombie/iso/objects/IsoThumpable
        // 1b8: ifeq 1d1
        // 1bb: aload 10
        // 1bd: checkcast zombie/iso/objects/IsoThumpable
        // 1c0: getfield zombie/iso/objects/IsoThumpable.isDoor Ljava/lang/Boolean;
        // 1c3: invokevirtual java/lang/Boolean.booleanValue ()Z
        // 1c6: ifeq 1d1
        // 1c9: getstatic zombie/iso/LosUtil$TestResults.ClearThroughOpenDoor Lzombie/iso/LosUtil$TestResults;
        // 1cc: astore 8
        // 1ce: goto 284
        // 1d1: aload 11
        // 1d3: getstatic zombie/iso/IsoObject$VisionResult.Unblocked Lzombie/iso/IsoObject$VisionResult;
        // 1d6: if_acmpne 1e9
        // 1d9: aload 10
        // 1db: instanceof zombie/iso/objects/IsoWindow
        // 1de: ifeq 1e9
        // 1e1: getstatic zombie/iso/LosUtil$TestResults.ClearThroughWindow Lzombie/iso/LosUtil$TestResults;
        // 1e4: astore 8
        // 1e6: goto 284
        // 1e9: aload 11
        // 1eb: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 1ee: if_acmpne 202
        // 1f1: aload 10
        // 1f3: instanceof zombie/iso/objects/IsoDoor
        // 1f6: ifeq 202
        // 1f9: iload 5
        // 1fb: ifne 202
        // 1fe: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 201: areturn
        // 202: aload 11
        // 204: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 207: if_acmpne 229
        // 20a: aload 10
        // 20c: instanceof zombie/iso/objects/IsoThumpable
        // 20f: ifeq 229
        // 212: aload 10
        // 214: checkcast zombie/iso/objects/IsoThumpable
        // 217: getfield zombie/iso/objects/IsoThumpable.isDoor Ljava/lang/Boolean;
        // 21a: invokevirtual java/lang/Boolean.booleanValue ()Z
        // 21d: ifeq 229
        // 220: iload 5
        // 222: ifne 229
        // 225: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 228: areturn
        // 229: aload 11
        // 22b: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 22e: if_acmpne 248
        // 231: aload 10
        // 233: instanceof zombie/iso/objects/IsoThumpable
        // 236: ifeq 248
        // 239: aload 10
        // 23b: checkcast zombie/iso/objects/IsoThumpable
        // 23e: invokevirtual zombie/iso/objects/IsoThumpable.isWindow ()Z
        // 241: ifeq 248
        // 244: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 247: areturn
        // 248: aload 11
        // 24a: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 24d: if_acmpne 25c
        // 250: aload 10
        // 252: instanceof zombie/iso/objects/IsoCurtain
        // 255: ifeq 25c
        // 258: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 25b: areturn
        // 25c: aload 11
        // 25e: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 261: if_acmpne 270
        // 264: aload 10
        // 266: instanceof zombie/iso/objects/IsoWindow
        // 269: ifeq 270
        // 26c: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 26f: areturn
        // 270: aload 11
        // 272: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 275: if_acmpne 284
        // 278: aload 10
        // 27a: instanceof zombie/iso/objects/IsoBarricade
        // 27d: ifeq 284
        // 280: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 283: areturn
        // 284: iinc 9 1
        // 287: goto 14d
        // 28a: aload 7
        // 28c: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 28f: invokevirtual java/util/ArrayList.isEmpty ()Z
        // 292: ifne 3d7
        // 295: bipush 0
        // 296: istore 9
        // 298: iload 9
        // 29a: aload 7
        // 29c: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 29f: invokevirtual java/util/ArrayList.size ()I
        // 2a2: if_icmpge 3d7
        // 2a5: aload 7
        // 2a7: getfield zombie/iso/IsoGridSquare.SpecialObjects Ljava/util/ArrayList;
        // 2aa: iload 9
        // 2ac: invokevirtual java/util/ArrayList.get (I)Ljava/lang/Object;
        // 2af: checkcast zombie/iso/IsoObject
        // 2b2: astore 10
        // 2b4: aload 10
        // 2b6: ifnonnull 2bd
        // 2b9: getstatic zombie/iso/LosUtil$TestResults.Clear Lzombie/iso/LosUtil$TestResults;
        // 2bc: areturn
        // 2bd: aload 10
        // 2bf: aload 0
        // 2c0: aload 7
        // 2c2: invokevirtual zombie/iso/IsoObject.TestVision (Lzombie/iso/IsoGridSquare;Lzombie/iso/IsoGridSquare;)Lzombie/iso/IsoObject$VisionResult;
        // 2c5: astore 11
        // 2c7: aload 11
        // 2c9: getstatic zombie/iso/IsoObject$VisionResult.NoEffect Lzombie/iso/IsoObject$VisionResult;
        // 2cc: if_acmpeq 3d1
        // 2cf: aload 11
        // 2d1: getstatic zombie/iso/IsoObject$VisionResult.Unblocked Lzombie/iso/IsoObject$VisionResult;
        // 2d4: if_acmpne 2f8
        // 2d7: aload 10
        // 2d9: instanceof zombie/iso/objects/IsoDoor
        // 2dc: ifeq 2f8
        // 2df: aload 10
        // 2e1: checkcast zombie/iso/objects/IsoDoor
        // 2e4: invokevirtual zombie/iso/objects/IsoDoor.IsOpen ()Z
        // 2e7: ifeq 2f0
        // 2ea: getstatic zombie/iso/LosUtil$TestResults.ClearThroughOpenDoor Lzombie/iso/LosUtil$TestResults;
        // 2ed: goto 2f3
        // 2f0: getstatic zombie/iso/LosUtil$TestResults.ClearThroughClosedDoor Lzombie/iso/LosUtil$TestResults;
        // 2f3: astore 8
        // 2f5: goto 3d1
        // 2f8: aload 11
        // 2fa: getstatic zombie/iso/IsoObject$VisionResult.Unblocked Lzombie/iso/IsoObject$VisionResult;
        // 2fd: if_acmpne 31e
        // 300: aload 10
        // 302: instanceof zombie/iso/objects/IsoThumpable
        // 305: ifeq 31e
        // 308: aload 10
        // 30a: checkcast zombie/iso/objects/IsoThumpable
        // 30d: getfield zombie/iso/objects/IsoThumpable.isDoor Ljava/lang/Boolean;
        // 310: invokevirtual java/lang/Boolean.booleanValue ()Z
        // 313: ifeq 31e
        // 316: getstatic zombie/iso/LosUtil$TestResults.ClearThroughOpenDoor Lzombie/iso/LosUtil$TestResults;
        // 319: astore 8
        // 31b: goto 3d1
        // 31e: aload 11
        // 320: getstatic zombie/iso/IsoObject$VisionResult.Unblocked Lzombie/iso/IsoObject$VisionResult;
        // 323: if_acmpne 336
        // 326: aload 10
        // 328: instanceof zombie/iso/objects/IsoWindow
        // 32b: ifeq 336
        // 32e: getstatic zombie/iso/LosUtil$TestResults.ClearThroughWindow Lzombie/iso/LosUtil$TestResults;
        // 331: astore 8
        // 333: goto 3d1
        // 336: aload 11
        // 338: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 33b: if_acmpne 34f
        // 33e: aload 10
        // 340: instanceof zombie/iso/objects/IsoDoor
        // 343: ifeq 34f
        // 346: iload 5
        // 348: ifne 34f
        // 34b: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 34e: areturn
        // 34f: aload 11
        // 351: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 354: if_acmpne 376
        // 357: aload 10
        // 359: instanceof zombie/iso/objects/IsoThumpable
        // 35c: ifeq 376
        // 35f: aload 10
        // 361: checkcast zombie/iso/objects/IsoThumpable
        // 364: getfield zombie/iso/objects/IsoThumpable.isDoor Ljava/lang/Boolean;
        // 367: invokevirtual java/lang/Boolean.booleanValue ()Z
        // 36a: ifeq 376
        // 36d: iload 5
        // 36f: ifne 376
        // 372: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 375: areturn
        // 376: aload 11
        // 378: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 37b: if_acmpne 395
        // 37e: aload 10
        // 380: instanceof zombie/iso/objects/IsoThumpable
        // 383: ifeq 395
        // 386: aload 10
        // 388: checkcast zombie/iso/objects/IsoThumpable
        // 38b: invokevirtual zombie/iso/objects/IsoThumpable.isWindow ()Z
        // 38e: ifeq 395
        // 391: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 394: areturn
        // 395: aload 11
        // 397: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 39a: if_acmpne 3a9
        // 39d: aload 10
        // 39f: instanceof zombie/iso/objects/IsoCurtain
        // 3a2: ifeq 3a9
        // 3a5: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 3a8: areturn
        // 3a9: aload 11
        // 3ab: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 3ae: if_acmpne 3bd
        // 3b1: aload 10
        // 3b3: instanceof zombie/iso/objects/IsoWindow
        // 3b6: ifeq 3bd
        // 3b9: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 3bc: areturn
        // 3bd: aload 11
        // 3bf: getstatic zombie/iso/IsoObject$VisionResult.Blocked Lzombie/iso/IsoObject$VisionResult;
        // 3c2: if_acmpne 3d1
        // 3c5: aload 10
        // 3c7: instanceof zombie/iso/objects/IsoBarricade
        // 3ca: ifeq 3d1
        // 3cd: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 3d0: areturn
        // 3d1: iinc 9 1
        // 3d4: goto 298
        // 3d7: aload 8
        // 3d9: astore 6
        // 3db: aload 0
        // 3dc: getfield zombie/iso/IsoGridSquare.visionMatrix I
        // 3df: iload 1
        // 3e0: bipush 1
        // 3e1: iadd
        // 3e2: iload 2
        // 3e3: bipush 1
        // 3e4: iadd
        // 3e5: iload 3
        // 3e6: bipush 1
        // 3e7: iadd
        // 3e8: invokestatic zombie/iso/IsoGridSquare.getMatrixBit (IIII)Z
        // 3eb: ifne 3f3
        // 3ee: aload 6
        // 3f0: goto 3f6
        // 3f3: getstatic zombie/iso/LosUtil$TestResults.Blocked Lzombie/iso/LosUtil$TestResults;
        // 3f6: areturn
        // 3f7: aload 6
        // 3f9: areturn
        return null;
    }

    public boolean TreatAsSolidFloor() {
        if (this.SolidFloorCached) {
            return this.SolidFloor;
        } else if (!this.Properties.Is(IsoFlagType.solidfloor) && !this.HasStairs()) {
            this.SolidFloor = false;
        } else {
            this.SolidFloor = true;
        }

        return false;
    }

    public void AddSpecialTileObject(IsoObject var1) {
        this.AddSpecialObject(var1);
    }

    public void renderCharacters(int var1, boolean var2, boolean var3) {
        if (this.z < var1) {
            if (!isOnScreenLast) {
            }

            if (var3) {
                IndieGL.glBlendFunc(770, 771);
            }

            if (this.MovingObjects.size() > 1) {
                Collections.sort(this.MovingObjects, comp);
            }

            int var4 = IsoCamera.frameState.playerIndex;
            ColorInfo var5 = this.lightInfo[var4];
            int var6 = this.StaticMovingObjects.size();

            for (int var7 = 0; var7 < var6; var7++) {
                IsoMovingObject var8 = this.StaticMovingObjects.get(var7);
                if (var8.sprite == null && !(var8 instanceof IsoDeadBody)
                    || var2 && (!(var8 instanceof IsoDeadBody) || this.HasStairs())
                    || !var2 && var8 instanceof IsoDeadBody && !this.HasStairs()) {
                    continue;
                }

                var8.render(var8.getX(), var8.getY(), var8.getZ(), var5, true, false, null);
            }

            var6 = this.MovingObjects.size();

            for (int var12 = 0; var12 < var6; var12++) {
                IsoMovingObject var13 = this.MovingObjects.get(var12);
                if (var13 != null && var13.sprite != null) {
                    boolean var9 = var13.bOnFloor;
                    if (var9 && var13 instanceof IsoZombie var10) {
                        var9 = var10.isProne();
                        if (!BaseVehicle.RENDER_TO_TEXTURE) {
                            var9 = false;
                        }
                    }

                    if (var2 && !var9 || !var2 && var9) {
                        continue;
                    }

                    var13.render(var13.getX(), var13.getY(), var13.getZ(), var5, true, false, null);
                }
            }
        }
    }

    public void renderDeferredCharacters(int var1) {
        if (!this.DeferedCharacters.isEmpty()) {
            if (this.DeferredCharacterTick != this.getCell().DeferredCharacterTick) {
                this.DeferedCharacters.clear();
            } else if (this.z >= var1) {
                this.DeferedCharacters.clear();
            } else if (PerformanceSettings.LightingFrameSkip != 3) {
                short var2 = this.getCell().getStencilValue2z(this.x, this.y, this.z - 1);
                this.getCell().setStencilValue2z(this.x, this.y, this.z - 1, var2);
                IndieGL.enableAlphaTest();
                IndieGL.glAlphaFunc(516, 0.0F);
                IndieGL.glStencilFunc(519, var2, 127);
                IndieGL.glStencilOp(7680, 7680, 7681);
                float var3 = IsoUtils.XToScreen((float)this.x, (float)this.y, (float)this.z, 0);
                float var4 = IsoUtils.YToScreen((float)this.x, (float)this.y, (float)this.z, 0);
                var3 = var3 - IsoCamera.frameState.OffX;
                var4 = var4 - IsoCamera.frameState.OffY;
                IndieGL.glColorMask(false, false, false, false);
                Texture.getWhite().renderwallnw(var3, var4, (float)(64 * Core.TileScale), (float)(32 * Core.TileScale), -1, -1, -1, -1, -1, -1);
                IndieGL.glColorMask(true, true, true, true);
                IndieGL.enableAlphaTest();
                IndieGL.glAlphaFunc(516, 0.0F);
                IndieGL.glStencilFunc(514, var2, 127);
                IndieGL.glStencilOp(7680, 7680, 7680);
                ColorInfo var5 = this.lightInfo[IsoCamera.frameState.playerIndex];
                Collections.sort(this.DeferedCharacters, comp);

                for (int var6 = 0; var6 < this.DeferedCharacters.size(); var6++) {
                    IsoGameCharacter var7 = this.DeferedCharacters.get(var6);
                    if (var7.sprite != null) {
                        var7.setbDoDefer(false);
                        var7.render(var7.getX(), var7.getY(), var7.getZ(), var5, true, false, null);
                        var7.renderObjectPicker(var7.getX(), var7.getY(), var7.getZ(), var5);
                        var7.setbDoDefer(true);
                    }
                }

                this.DeferedCharacters.clear();
                IndieGL.glAlphaFunc(516, 0.0F);
                IndieGL.glStencilFunc(519, 1, 255);
                IndieGL.glStencilOp(7680, 7680, 7680);
            }
        }
    }

    public void switchLight(boolean var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (var3 instanceof IsoLightSwitch) {
                ((IsoLightSwitch)var3).setActive(var1);
            }
        }
    }

    public void removeLightSwitch() {
        for (int var1 = 0; var1 < this.Objects.size(); var1++) {
            IsoObject var2 = (IsoObject)this.Objects.get(var1);
            if (var2 instanceof IsoLightSwitch) {
                this.Objects.remove(var1);
                var1--;
            }
        }
    }

    public boolean IsOnScreen() {
        return this.IsOnScreen(false);
    }

    public boolean IsOnScreen(boolean var1) {
        if (this.CachedScreenValue != Core.TileScale) {
            this.CachedScreenX = IsoUtils.XToScreen((float)this.x, (float)this.y, (float)this.z, 0);
            this.CachedScreenY = IsoUtils.YToScreen((float)this.x, (float)this.y, (float)this.z, 0);
            this.CachedScreenValue = Core.TileScale;
        }

        float var2 = this.CachedScreenX;
        float var3 = this.CachedScreenY;
        var2 = var2 - IsoCamera.frameState.OffX;
        var3 = var3 - IsoCamera.frameState.OffY;
        int var4 = var1 ? 32 * Core.TileScale : 0;
        if (this.hasTree) {
            int var5 = 384 * Core.TileScale / 2 - 96 * Core.TileScale;
            int var6 = 256 * Core.TileScale - 32 * Core.TileScale;
            if (var2 + (float)var5 <= (float)(0 - var4)) {
                return false;
            } else if (var3 + (float)(32 * Core.TileScale) <= (float)(0 - var4)) {
                return false;
            } else if (var2 - (float)var5 >= (float)(IsoCamera.frameState.OffscreenWidth + var4)) {
                return false;
            } else if (var3 - (float)var6 >= (float)(IsoCamera.frameState.OffscreenHeight + var4)) {
                return false;
            } else {
                return true;
            }
        } else if (var2 + (float)(32 * Core.TileScale) <= (float)(0 - var4)) {
            return false;
        } else if (var3 + (float)(32 * Core.TileScale) <= (float)(0 - var4)) {
            return false;
        } else if (var2 - (float)(32 * Core.TileScale) >= (float)(IsoCamera.frameState.OffscreenWidth + var4)) {
            return false;
        } else if (var3 - (float)(96 * Core.TileScale) >= (float)(IsoCamera.frameState.OffscreenHeight + var4)) {
            return false;
        } else {
            return true;
        }
    }

    void cacheLightInfo() {
        int var1 = IsoCamera.frameState.playerIndex;
        this.lightInfo[var1] = this.lighting[var1].lightInfo();
    }

    public void setLightInfoServerGUIOnly(ColorInfo var1) {
        this.lightInfo[0] = var1;
    }

    int renderFloor(Shader var1) {
        try {
            s_performance.renderFloor.start();
            int var2 = this.renderFloorInternal(var1);
        } finally {
            s_performance.renderFloor.end();
        }

        return 0;
    }

    private int renderFloorInternal(Shader var1) {
        int var2 = IsoCamera.frameState.playerIndex;
        ColorInfo var3 = this.lightInfo[var2];
        IsoGridSquare var4 = IsoCamera.frameState.CamCharacterSquare;
        boolean var5 = this.lighting[var2].bCouldSee();
        float var6 = this.lighting[var2].darkMulti();
        boolean var7 = GameClient.bClient && IsoPlayer.players[var2] != null && IsoPlayer.players[var2].isSeeNonPvpZone();
        boolean var8 = Core.bDebug && GameClient.bClient && SafeHouse.isSafeHouse(this, null, true) != null;
        boolean var9 = true;
        float var10 = 1.0F;
        float var11 = 1.0F;
        if (var4 != null) {
            int var12 = this.getRoomID();
            if (var12 != -1) {
                int var13 = IsoWorld.instance.CurrentCell.GetEffectivePlayerRoomId();
                if (var13 == -1 && IsoWorld.instance.CurrentCell.CanBuildingSquareOccludePlayer(this, var2)) {
                    var9 = false;
                    var10 = 1.0F;
                    var11 = 1.0F;
                } else if (!var5 && var12 != var13 && var6 < 0.5F) {
                    var9 = false;
                    var10 = 0.0F;
                    var11 = var6 * 2.0F;
                }
            }
        }

        IsoWaterGeometry var30 = this.z == 0 ? this.getWater() : null;
        boolean var31 = var30 != null && var30.bShore;
        float var14 = var30 == null ? 0.0F : var30.depth[0];
        float var15 = var30 == null ? 0.0F : var30.depth[3];
        float var16 = var30 == null ? 0.0F : var30.depth[2];
        float var17 = var30 == null ? 0.0F : var30.depth[1];
        byte var18 = 0;
        int var19 = this.Objects.size();
        IsoObject[] var20 = (IsoObject[])this.Objects.getElements();

        for (int var21 = 0; var21 < var19; var21++) {
            IsoObject var22 = var20[var21];
            if (var7 && (var22.highlightFlags & 1) == 0) {
                var22.setHighlighted(true);
                if (NonPvpZone.getNonPvpZone(this.x, this.y) != null) {
                    var22.setHighlightColor(0.6F, 0.6F, 1.0F, 0.5F);
                } else {
                    var22.setHighlightColor(1.0F, 0.6F, 0.6F, 0.5F);
                }
            }

            if (var8) {
                var22.setHighlighted(true);
                var22.setHighlightColor(1.0F, 0.0F, 0.0F, 1.0F);
            }

            boolean var23 = true;
            if (var22.sprite != null && !var22.sprite.solidfloor && var22.sprite.renderLayer != 1) {
                var23 = false;
                var18 |= 4;
            }

            if (!(var22 instanceof IsoFire) && !(var22 instanceof IsoCarBatteryCharger)) {
            }

            var23 = false;
            var18 |= 4;
        }

        if ((this.getCell().rainIntensity > 0 || RainManager.isRaining() && RainManager.RainIntensity > 0.0F)
            && this.isExteriorCache
            && !this.isVegitationCache
            && this.isSolidFloorCache
            && this.isCouldSee(var2)) {
            if (!IsoCamera.frameState.Paused) {
                int var32 = this.getCell().rainIntensity == 0
                    ? (int)Math.min(Math.floor((double)(RainManager.RainIntensity / 0.2F)) + 1.0, 5.0)
                    : this.getCell().rainIntensity;
                if (this.splashFrame < 0.0F && Rand.Next(Rand.AdjustForFramerate((int)(5.0F / (float)var32) * 100)) == 0) {
                    this.splashFrame = 0.0F;
                }
            }

            if (this.splashFrame >= 0.0F) {
                int var33 = (int)(this.splashFrame * 4.0F);
                if (rainsplashCache[var33] == null) {
                    rainsplashCache[var33] = "RainSplash_00_" + var33;
                }

                Texture var34 = Texture.getSharedTexture(rainsplashCache[var33]);
                if (var34 != null) {
                    float var35 = IsoUtils.XToScreen((float)this.x + this.splashX, (float)this.y + this.splashY, (float)this.z, 0) - IsoCamera.frameState.OffX;
                    float var38 = IsoUtils.YToScreen((float)this.x + this.splashX, (float)this.y + this.splashY, (float)this.z, 0) - IsoCamera.frameState.OffY;
                    var35 = var35 - (float)(var34.getWidth() / 2 * Core.TileScale);
                    var38 = var38 - (float)(var34.getHeight() / 2 * Core.TileScale);
                    float var40 = 0.6F * (this.getCell().rainIntensity > 0 ? 1.0F : RainManager.RainIntensity);
                    float var41 = Core.getInstance().RenderShader != null ? 0.6F : 1.0F;
                    SpriteRenderer.instance
                        .render(
                            var34,
                            var35,
                            var38,
                            (float)(var34.getWidth() * Core.TileScale),
                            (float)(var34.getHeight() * Core.TileScale),
                            0.8F * var3.r,
                            0.9F * var3.g,
                            1.0F * var3.b,
                            var40 * var41,
                            null
                        );
                }

                if (!IsoCamera.frameState.Paused && this.splashFrameNum != IsoCamera.frameState.frameCount) {
                    this.splashFrame = this.splashFrame + 0.08F * (30.0F / (float)PerformanceSettings.getLockFPS());
                    if (this.splashFrame >= 1.0F) {
                        this.splashX = Rand.Next(0.1F, 0.9F);
                        this.splashY = Rand.Next(0.1F, 0.9F);
                        this.splashFrame = -1.0F;
                    }

                    this.splashFrameNum = IsoCamera.frameState.frameCount;
                }
            }
        } else {
            this.splashFrame = -1.0F;
        }

        return 0;
    }

    private boolean isSpriteOnSouthOrEastWall(IsoObject var1) {
        if (var1 instanceof IsoBarricade) {
            return var1.getDir() == IsoDirections.S || var1.getDir() == IsoDirections.E;
        } else if (var1 instanceof IsoCurtain var3) {
            return var3.getType() == IsoObjectType.curtainS || var3.getType() == IsoObjectType.curtainE;
        } else {
            PropertyContainer var2 = var1.getProperties();
            return var2 != null && (var2.Is(IsoFlagType.attachedE) || var2.Is(IsoFlagType.attachedS));
        }
    }

    public void RenderOpenDoorOnly() {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:28
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:310)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:181)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 00: aload 0
        // 01: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 04: invokevirtual zombie/util/list/PZArrayList.size ()I
        // 07: istore 1
        // 08: aload 0
        // 09: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 0c: invokevirtual zombie/util/list/PZArrayList.getElements ()[Ljava/lang/Object;
        // 0f: checkcast [Lzombie/iso/IsoObject;
        // 12: astore 2
        // 13: bipush 0
        // 14: istore 3
        // 15: iload 1
        // 16: bipush 1
        // 17: isub
        // 18: istore 4
        // 1a: iload 3
        // 1b: istore 5
        // 1d: iload 5
        // 1f: iload 4
        // 21: if_icmpgt 72
        // 24: aload 2
        // 25: iload 5
        // 27: aaload
        // 28: astore 6
        // 2a: aload 6
        // 2c: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 2f: ifnonnull 35
        // 32: goto 6c
        // 35: aload 6
        // 37: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 3a: invokevirtual zombie/iso/sprite/IsoSprite.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 3d: getstatic zombie/iso/SpriteDetails/IsoFlagType.attachedN Lzombie/iso/SpriteDetails/IsoFlagType;
        // 40: invokevirtual zombie/core/properties/PropertyContainer.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 43: ifne 57
        // 46: aload 6
        // 48: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 4b: invokevirtual zombie/iso/sprite/IsoSprite.getProperties ()Lzombie/core/properties/PropertyContainer;
        // 4e: getstatic zombie/iso/SpriteDetails/IsoFlagType.attachedW Lzombie/iso/SpriteDetails/IsoFlagType;
        // 51: invokevirtual zombie/core/properties/PropertyContainer.Is (Lzombie/iso/SpriteDetails/IsoFlagType;)Z
        // 54: ifeq 6c
        // 57: aload 6
        // 59: aload 0
        // 5a: getfield zombie/iso/IsoGridSquare.x I
        // 5d: i2f
        // 5e: aload 0
        // 5f: getfield zombie/iso/IsoGridSquare.y I
        // 62: i2f
        // 63: aload 0
        // 64: getfield zombie/iso/IsoGridSquare.z I
        // 67: i2f
        // 68: bipush 0
        // 69: invokevirtual zombie/iso/IsoObject.renderFxMask (FFFZ)V
        // 6c: iinc 5 1
        // 6f: goto 1d
        // 72: goto 7a
        // 75: astore 3
        // 76: aload 3
        // 77: invokestatic zombie/core/logger/ExceptionLogger.logException (Ljava/lang/Throwable;)V
        // 7a: return
    }

    public boolean RenderMinusFloorFxMask(int var1, boolean var2, boolean var3) {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:153
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:310)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:181)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 000: bipush 0
        // 001: istore 4
        // 003: aload 0
        // 004: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 007: invokevirtual zombie/util/list/PZArrayList.size ()I
        // 00a: istore 5
        // 00c: aload 0
        // 00d: getfield zombie/iso/IsoGridSquare.Objects Lzombie/util/list/PZArrayList;
        // 010: invokevirtual zombie/util/list/PZArrayList.getElements ()[Ljava/lang/Object;
        // 013: checkcast [Lzombie/iso/IsoObject;
        // 016: astore 6
        // 018: invokestatic java/lang/System.currentTimeMillis ()J
        // 01b: lstore 7
        // 01d: iload 2
        // 01e: ifeq 028
        // 021: iload 5
        // 023: bipush 1
        // 024: isub
        // 025: goto 029
        // 028: bipush 0
        // 029: istore 9
        // 02b: iload 2
        // 02c: ifeq 033
        // 02f: bipush 0
        // 030: goto 037
        // 033: iload 5
        // 035: bipush 1
        // 036: isub
        // 037: istore 10
        // 039: iload 9
        // 03b: istore 11
        // 03d: iload 2
        // 03e: ifeq 04b
        // 041: iload 11
        // 043: iload 10
        // 045: if_icmplt 235
        // 048: goto 052
        // 04b: iload 11
        // 04d: iload 10
        // 04f: if_icmpgt 235
        // 052: aload 6
        // 054: iload 11
        // 056: aaload
        // 057: astore 12
        // 059: aload 12
        // 05b: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 05e: ifnonnull 064
        // 061: goto 224
        // 064: bipush 1
        // 065: istore 13
        // 067: aload 12
        // 069: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 06c: invokevirtual zombie/iso/sprite/IsoSprite.getType ()Lzombie/iso/SpriteDetails/IsoObjectType;
        // 06f: astore 14
        // 071: aload 12
        // 073: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 076: getfield zombie/iso/sprite/IsoSprite.solidfloor Z
        // 079: ifne 088
        // 07c: aload 12
        // 07e: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 081: getfield zombie/iso/sprite/IsoSprite.renderLayer B
        // 084: bipush 1
        // 085: if_icmpne 08b
        // 088: bipush 0
        // 089: istore 13
        // 08b: aload 0
        // 08c: getfield zombie/iso/IsoGridSquare.z I
        // 08f: iload 1
        // 090: if_icmplt 0a1
        // 093: aload 12
        // 095: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 098: getfield zombie/iso/sprite/IsoSprite.alwaysDraw Z
        // 09b: ifne 0a1
        // 09e: bipush 0
        // 09f: istore 13
        // 0a1: aload 12
        // 0a3: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 0a6: getfield zombie/iso/sprite/IsoSprite.isBush Z
        // 0a9: ifne 0c2
        // 0ac: aload 12
        // 0ae: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 0b1: getfield zombie/iso/sprite/IsoSprite.canBeRemoved Z
        // 0b4: ifne 0c2
        // 0b7: aload 12
        // 0b9: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 0bc: getfield zombie/iso/sprite/IsoSprite.attachedFloor Z
        // 0bf: ifeq 0c6
        // 0c2: bipush 1
        // 0c3: goto 0c7
        // 0c6: bipush 0
        // 0c7: istore 15
        // 0c9: iload 3
        // 0ca: ifeq 0dc
        // 0cd: iload 15
        // 0cf: ifeq 224
        // 0d2: aload 0
        // 0d3: getfield zombie/iso/IsoGridSquare.bFlattenGrassEtc Z
        // 0d6: ifne 0dc
        // 0d9: goto 224
        // 0dc: iload 3
        // 0dd: ifne 0ef
        // 0e0: iload 15
        // 0e2: ifeq 0ef
        // 0e5: aload 0
        // 0e6: getfield zombie/iso/IsoGridSquare.bFlattenGrassEtc Z
        // 0e9: ifeq 0ef
        // 0ec: goto 224
        // 0ef: aload 14
        // 0f1: getstatic zombie/iso/SpriteDetails/IsoObjectType.WestRoofB Lzombie/iso/SpriteDetails/IsoObjectType;
        // 0f4: if_acmpeq 107
        // 0f7: aload 14
        // 0f9: getstatic zombie/iso/SpriteDetails/IsoObjectType.WestRoofM Lzombie/iso/SpriteDetails/IsoObjectType;
        // 0fc: if_acmpeq 107
        // 0ff: aload 14
        // 101: getstatic zombie/iso/SpriteDetails/IsoObjectType.WestRoofT Lzombie/iso/SpriteDetails/IsoObjectType;
        // 104: if_acmpne 122
        // 107: aload 0
        // 108: getfield zombie/iso/IsoGridSquare.z I
        // 10b: iload 1
        // 10c: bipush 1
        // 10d: isub
        // 10e: if_icmpne 122
        // 111: aload 0
        // 112: getfield zombie/iso/IsoGridSquare.z I
        // 115: getstatic zombie/iso/IsoCamera.CamCharacter Lzombie/characters/IsoGameCharacter;
        // 118: invokevirtual zombie/characters/IsoGameCharacter.getZ ()F
        // 11b: f2i
        // 11c: if_icmpne 122
        // 11f: bipush 0
        // 120: istore 13
        // 122: aload 0
        // 123: aload 12
        // 125: invokevirtual zombie/iso/IsoGridSquare.isSpriteOnSouthOrEastWall (Lzombie/iso/IsoObject;)Z
        // 128: ifeq 138
        // 12b: iload 2
        // 12c: ifne 132
        // 12f: bipush 0
        // 130: istore 13
        // 132: bipush 1
        // 133: istore 4
        // 135: goto 13f
        // 138: iload 2
        // 139: ifeq 13f
        // 13c: bipush 0
        // 13d: istore 13
        // 13f: iload 13
        // 141: ifeq 224
        // 144: aload 12
        // 146: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 149: getfield zombie/iso/sprite/IsoSprite.cutW Z
        // 14c: ifne 15a
        // 14f: aload 12
        // 151: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 154: getfield zombie/iso/sprite/IsoSprite.cutN Z
        // 157: ifeq 20f
        // 15a: getstatic zombie/iso/IsoCamera.frameState Lzombie/iso/IsoCamera$FrameState;
        // 15d: getfield zombie/iso/IsoCamera$FrameState.playerIndex I
        // 160: istore 16
        // 162: aload 12
        // 164: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 167: getfield zombie/iso/sprite/IsoSprite.cutN Z
        // 16a: istore 17
        // 16c: aload 12
        // 16e: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 171: getfield zombie/iso/sprite/IsoSprite.cutW Z
        // 174: istore 18
        // 176: aload 0
        // 177: getfield zombie/iso/IsoGridSquare.nav [Lzombie/iso/IsoGridSquare;
        // 17a: getstatic zombie/iso/IsoDirections.S Lzombie/iso/IsoDirections;
        // 17d: invokevirtual zombie/iso/IsoDirections.index ()I
        // 180: aaload
        // 181: astore 19
        // 183: aload 0
        // 184: getfield zombie/iso/IsoGridSquare.nav [Lzombie/iso/IsoGridSquare;
        // 187: getstatic zombie/iso/IsoDirections.E Lzombie/iso/IsoDirections;
        // 18a: invokevirtual zombie/iso/IsoDirections.index ()I
        // 18d: aaload
        // 18e: astore 20
        // 190: aload 19
        // 192: ifnull 1a5
        // 195: aload 19
        // 197: iload 16
        // 199: lload 7
        // 19b: invokevirtual zombie/iso/IsoGridSquare.getPlayerCutawayFlag (IJ)Z
        // 19e: ifeq 1a5
        // 1a1: bipush 1
        // 1a2: goto 1a6
        // 1a5: bipush 0
        // 1a6: istore 21
        // 1a8: aload 0
        // 1a9: iload 16
        // 1ab: lload 7
        // 1ad: invokevirtual zombie/iso/IsoGridSquare.getPlayerCutawayFlag (IJ)Z
        // 1b0: istore 22
        // 1b2: aload 20
        // 1b4: ifnull 1c7
        // 1b7: aload 20
        // 1b9: iload 16
        // 1bb: lload 7
        // 1bd: invokevirtual zombie/iso/IsoGridSquare.getPlayerCutawayFlag (IJ)Z
        // 1c0: ifeq 1c7
        // 1c3: bipush 1
        // 1c4: goto 1c8
        // 1c7: bipush 0
        // 1c8: istore 23
        // 1ca: iload 17
        // 1cc: ifeq 1dc
        // 1cf: iload 18
        // 1d1: ifeq 1dc
        // 1d4: getstatic zombie/iso/IsoDirections.NW Lzombie/iso/IsoDirections;
        // 1d7: astore 24
        // 1d9: goto 1fb
        // 1dc: iload 17
        // 1de: ifeq 1e9
        // 1e1: getstatic zombie/iso/IsoDirections.N Lzombie/iso/IsoDirections;
        // 1e4: astore 24
        // 1e6: goto 1fb
        // 1e9: iload 18
        // 1eb: ifeq 1f6
        // 1ee: getstatic zombie/iso/IsoDirections.W Lzombie/iso/IsoDirections;
        // 1f1: astore 24
        // 1f3: goto 1fb
        // 1f6: getstatic zombie/iso/IsoDirections.W Lzombie/iso/IsoDirections;
        // 1f9: astore 24
        // 1fb: aload 0
        // 1fc: aload 12
        // 1fe: getfield zombie/iso/IsoObject.sprite Lzombie/iso/sprite/IsoSprite;
        // 201: aload 24
        // 203: iload 21
        // 205: iload 22
        // 207: iload 23
        // 209: invokevirtual zombie/iso/IsoGridSquare.DoCutawayShaderSprite (Lzombie/iso/sprite/IsoSprite;Lzombie/iso/IsoDirections;ZZZ)V
        // 20c: goto 224
        // 20f: aload 12
        // 211: aload 0
        // 212: getfield zombie/iso/IsoGridSquare.x I
        // 215: i2f
        // 216: aload 0
        // 217: getfield zombie/iso/IsoGridSquare.y I
        // 21a: i2f
        // 21b: aload 0
        // 21c: getfield zombie/iso/IsoGridSquare.z I
        // 21f: i2f
        // 220: bipush 0
        // 221: invokevirtual zombie/iso/IsoObject.renderFxMask (FFFZ)V
        // 224: iload 11
        // 226: iload 2
        // 227: ifeq 22e
        // 22a: bipush -1
        // 22b: goto 22f
        // 22e: bipush 1
        // 22f: iadd
        // 230: istore 11
        // 232: goto 03d
        // 235: goto 23f
        // 238: astore 9
        // 23a: aload 9
        // 23c: invokestatic zombie/core/logger/ExceptionLogger.logException (Ljava/lang/Throwable;)V
        // 23f: iload 4
        // 241: ireturn
        return false;
    }

    private boolean isWindowOrWindowFrame(IsoObject var1, boolean var2) {
        if (var1 != null && var1.sprite != null) {
            if (var2 && var1.sprite.getProperties().Is(IsoFlagType.windowN)) {
                return true;
            } else if (!var2 && var1.sprite.getProperties().Is(IsoFlagType.windowW)) {
                return true;
            } else {
                IsoThumpable var3 = (IsoThumpable)Type.tryCastTo(var1, IsoThumpable.class);
                if (var3 != null && var3.isWindow()) {
                    return var2 == var3.getNorth();
                } else {
                    return IsoWindowFrame.isWindowFrame(var1, var2);
                }
            }
        } else {
            return false;
        }
    }

    boolean renderMinusFloor(int var1, boolean var2, boolean var3, boolean var4, boolean var5, boolean var6, Shader var7) {
        boolean var8 = false;
        if (!this.localTemporaryObjects.isEmpty()) {
            var8 = this.renderMinusFloor(this.localTemporaryObjects, var1, var2, var3, var4, var5, var6, var7);
        }

        return this.renderMinusFloor(this.Objects, var1, var2, var3, var4, var5, var6, var7) || var8;
    }

    boolean renderMinusFloor(PZArrayList<IsoObject> var1, int var2, boolean var3, boolean var4, boolean var5, boolean var6, boolean var7, Shader var8) {
        if (!DebugOptions.instance.Terrain.RenderTiles.IsoGridSquare.RenderMinusFloor.getValue()) {
            return false;
        } else {
            IndieGL.glBlendFunc(770, 771);
            int var9 = 0;
            isOnScreenLast = this.IsOnScreen();
            int var10 = IsoCamera.frameState.playerIndex;
            IsoGridSquare var11 = IsoCamera.frameState.CamCharacterSquare;
            ColorInfo var12 = this.lightInfo[var10];
            boolean var13 = this.lighting[var10].bCouldSee();
            float var14 = this.lighting[var10].darkMulti();
            boolean var15 = IsoWorld.instance.CurrentCell.CanBuildingSquareOccludePlayer(this, var10);
            var12.a = 1.0F;
            defColorInfo.r = 1.0F;
            defColorInfo.g = 1.0F;
            defColorInfo.b = 1.0F;
            defColorInfo.a = 1.0F;
            if (Core.bDebug && DebugOptions.instance.DebugDraw_SkipWorldShading.getValue()) {
                var12 = defColorInfo;
            }

            label759: {
                float var16 = this.CachedScreenX - IsoCamera.frameState.OffX;
                float var17 = this.CachedScreenY - IsoCamera.frameState.OffY;
                boolean var18 = true;
                IsoCell var19 = this.getCell();
                if (!(var16 + (float)(32 * Core.TileScale) <= (float)var19.StencilX1)
                    && !(var16 - (float)(32 * Core.TileScale) >= (float)var19.StencilX2)
                    && !(var17 + (float)(32 * Core.TileScale) <= (float)var19.StencilY1)
                    && !(var17 - (float)(96 * Core.TileScale) >= (float)var19.StencilY2)) {
                    break label759;
                }

                var18 = false;
            }

            boolean var20 = false;
            int var21 = var1.size();
            IsoObject[] var22 = (IsoObject[])var1.getElements();
            tempWorldInventoryObjects.clear();
            int var23 = var3 ? var21 - 1 : 0;
            int var24 = var3 ? 0 : var21 - 1;
            boolean var25 = false;
            boolean var26 = false;
            boolean var27 = false;
            boolean var28 = false;
            if (!var3) {
                for (int var29 = var23; var29 <= var24; var29++) {
                    IsoObject var30;
                    var30 = var22[var29];
                    label744:
                    if (this.isWindowOrWindowFrame(var30, true)) {
                        if (!var6 && !var7) {
                            break label744;
                        }

                        IsoGridSquare var31 = this.nav[IsoDirections.N.index()];
                        var27 = var13 || var31 != null && var31.isCouldSee(var10);
                    }

                    label728:
                    if (this.isWindowOrWindowFrame(var30, false)) {
                        if (!var6 && !var5) {
                            break label728;
                        }

                        IsoGridSquare var50 = this.nav[IsoDirections.W.index()];
                        var28 = var13 || var50 != null && var50.isCouldSee(var10);
                    }

                    label712:
                    if (var30.sprite != null) {
                        if (var30.sprite.getType() != IsoObjectType.doorFrN && var30.sprite.getType() != IsoObjectType.doorN || !var6 && !var7) {
                            break label712;
                        }

                        IsoGridSquare var51 = this.nav[IsoDirections.N.index()];
                        var25 = var13 || var51 != null && var51.isCouldSee(var10);
                    }

                    if (var30.sprite != null) {
                        if (var30.sprite.getType() != IsoObjectType.doorFrW && var30.sprite.getType() != IsoObjectType.doorW || !var6 && !var5) {
                            continue;
                        }

                        IsoGridSquare var52 = this.nav[IsoDirections.W.index()];
                        var26 = var13 || var52 != null && var52.isCouldSee(var10);
                    }
                }
            }

            int var47 = IsoWorld.instance.CurrentCell.GetEffectivePlayerRoomId();
            bWallCutawayN = false;
            bWallCutawayW = false;

            for (int var48 = var23; var3 ? var48 >= var24 : var48 <= var24; var48 += var3 ? -1 : 1) {
                IsoObject var53 = var22[var48];
                boolean var32 = true;
                IsoObjectType var33 = IsoObjectType.MAX;
                if (var53.sprite != null) {
                    var33 = var53.sprite.getType();
                }

                CircleStencil = false;
                label668:
                if (var53.sprite != null) {
                    if (!var53.sprite.solidfloor && var53.sprite.renderLayer != 1) {
                        break label668;
                    }

                    var32 = false;
                }

                if (var53 instanceof IsoFire) {
                    var32 = !var4;
                }

                label661:
                if (this.z >= var2) {
                    if (var53.sprite != null && var53.sprite.alwaysDraw) {
                        break label661;
                    }

                    var32 = false;
                }

                boolean var34 = var53.sprite != null && (var53.sprite.isBush || var53.sprite.canBeRemoved || var53.sprite.attachedFloor);
                if (var4 && (!var34 || !this.bFlattenGrassEtc) || !var4 && var34 && this.bFlattenGrassEtc) {
                    continue;
                }

                if (var53.sprite != null
                    && (var33 == IsoObjectType.WestRoofB || var33 == IsoObjectType.WestRoofM || var33 == IsoObjectType.WestRoofT)
                    && this.z == var2 - 1
                    && this.z == (int)IsoCamera.CamCharacter.getZ()) {
                    var32 = false;
                }

                boolean var35 = var33 == IsoObjectType.doorFrW || var33 == IsoObjectType.doorW || var53.sprite != null && var53.sprite.cutW;
                boolean var36 = var33 == IsoObjectType.doorFrN || var33 == IsoObjectType.doorN || var53.sprite != null && var53.sprite.cutN;
                boolean var37 = var53 instanceof IsoDoor && ((IsoDoor)var53).open || var53 instanceof IsoThumpable && ((IsoThumpable)var53).open;
                boolean var38 = var53.container != null;
                boolean var39 = var53.sprite != null && var53.sprite.getProperties().Is(IsoFlagType.waterPiped);
                if (var53.sprite == null || var33 != IsoObjectType.MAX || var53 instanceof IsoDoor || var53 instanceof IsoWindow || var38 || var39) {
                }

                if (!var35 && var53.sprite.getProperties().Is(IsoFlagType.attachedW) && (var15 || var5 || var6)) {
                    var32 = !bWallCutawayW;
                } else {
                    label842: {
                        if (var36 || !var53.sprite.getProperties().Is(IsoFlagType.attachedN) || !var15 && !var6 && !var7) {
                            break label842;
                        }

                        var32 = !bWallCutawayN;
                    }
                }
            }

            Arrays.sort(
                (IsoWorldInventoryObject[])tempWorldInventoryObjects.getElements(),
                0,
                tempWorldInventoryObjects.size(),
                (var0, var1x) -> {
                    float var2x = ((IsoWorldInventoryObject)var0).xoff * ((IsoWorldInventoryObject)var0).xoff
                        + ((IsoWorldInventoryObject)var0).yoff * ((IsoWorldInventoryObject)var0).yoff;
                    float var3x = ((IsoWorldInventoryObject)var1x).xoff * ((IsoWorldInventoryObject)var1x).xoff
                        + ((IsoWorldInventoryObject)var1x).yoff * ((IsoWorldInventoryObject)var1x).yoff;
                    if (var2x == var3x) {
                        return 0;
                    } else {
                        return var2x > var3x ? 1 : -1;
                    }
                }
            );
        }

        return false;
    }

    void RereouteWallMaskTo(IsoObject var1) {
        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (!var3.sprite.getProperties().Is(IsoFlagType.collideW) && !var3.sprite.getProperties().Is(IsoFlagType.collideN)) {
                continue;
            }

            var3.rerouteMask = var1;
        }
    }

    void setBlockedGridPointers(GetSquare var1) {
        this.w = var1.getGridSquare(this.x - 1, this.y, this.z);
        this.e = var1.getGridSquare(this.x + 1, this.y, this.z);
        this.s = var1.getGridSquare(this.x, this.y + 1, this.z);
        this.n = var1.getGridSquare(this.x, this.y - 1, this.z);
        this.ne = var1.getGridSquare(this.x + 1, this.y - 1, this.z);
        this.nw = var1.getGridSquare(this.x - 1, this.y - 1, this.z);
        this.se = var1.getGridSquare(this.x + 1, this.y + 1, this.z);
        this.sw = var1.getGridSquare(this.x - 1, this.y + 1, this.z);
        if (this.s != null && this.testPathFindAdjacent(null, this.s.x - this.x, this.s.y - this.y, this.s.z - this.z, var1)) {
            this.s = null;
        }

        if (this.w != null && this.testPathFindAdjacent(null, this.w.x - this.x, this.w.y - this.y, this.w.z - this.z, var1)) {
            this.w = null;
        }

        if (this.n != null && this.testPathFindAdjacent(null, this.n.x - this.x, this.n.y - this.y, this.n.z - this.z, var1)) {
            this.n = null;
        }

        if (this.e != null && this.testPathFindAdjacent(null, this.e.x - this.x, this.e.y - this.y, this.e.z - this.z, var1)) {
            this.e = null;
        }

        if (this.sw != null && this.testPathFindAdjacent(null, this.sw.x - this.x, this.sw.y - this.y, this.sw.z - this.z, var1)) {
            this.sw = null;
        }

        if (this.se != null && this.testPathFindAdjacent(null, this.se.x - this.x, this.se.y - this.y, this.se.z - this.z, var1)) {
            this.se = null;
        }

        if (this.nw != null && this.testPathFindAdjacent(null, this.nw.x - this.x, this.nw.y - this.y, this.nw.z - this.z, var1)) {
            this.nw = null;
        }

        if (this.ne != null && this.testPathFindAdjacent(null, this.ne.x - this.x, this.ne.y - this.y, this.ne.z - this.z, var1)) {
            this.ne = null;
        }
    }

    public IsoObject getContainerItem(String var1) {
        int var2 = this.getObjects().size();
        IsoObject[] var3 = (IsoObject[])this.getObjects().getElements();

        for (int var4 = 0; var4 < var2; var4++) {
            IsoObject var5 = var3[var4];
            if (var5.getContainer() != null && var1.equals(var5.getContainer().getType())) {
                return var5;
            }
        }

        return null;
    }

    @Deprecated
    public void StartFire() {
    }

    public void explode() {
        IsoFireManager.explode(this.getCell(), this, 100000);
    }

    public int getHourLastSeen() {
        return this.hourLastSeen;
    }

    public float getHoursSinceLastSeen() {
        return (float)GameTime.instance.getWorldAgeHours() - (float)this.hourLastSeen;
    }

    public void CalcVisibility(int var1) {
        IsoPlayer var2 = IsoPlayer.players[var1];
        ILighting var3 = this.lighting[var1];
        var3.bCanSee(false);
        var3.bCouldSee(false);
        if (!GameServer.bServer && (var2 == null || var2.isDead() && var2.ReanimatedCorpse == null)) {
            var3.bSeen(true);
            var3.bCanSee(true);
            var3.bCouldSee(true);
        } else if (var2 != null) {
            LightInfo var4 = var2.getLightInfo2();
            IsoGridSquare var5 = var4.square;
            if (var5 != null) {
                IsoChunk var6 = this.getChunk();
                if (var6 != null) {
                    tempo.x = (float)this.x + 0.5F;
                    tempo.y = (float)this.y + 0.5F;
                    tempo2.x = var4.x;
                    tempo2.y = var4.y;
                    tempo2.x = tempo2.x - tempo.x;
                    tempo2.y = tempo2.y - tempo.y;
                    Vector2 var7 = tempo;
                    float var8 = tempo2.getLength();
                    tempo2.normalize();
                    if (var2 instanceof IsoSurvivor) {
                        var2.setForwardDirection(var7);
                        var4.angleX = var7.x;
                        var4.angleY = var7.y;
                    }

                    var7.x = var4.angleX;
                    var7.y = var4.angleY;
                    var7.normalize();
                    float var9 = tempo2.dot(var7);
                    if (var5 == this) {
                        var9 = -1.0F;
                    }

                    if (!GameServer.bServer) {
                        float var10 = var2.getStats().fatigue - 0.6F;
                        if (var10 < 0.0F) {
                            var10 = 0.0F;
                        }

                        var10 = var10 * 2.5F;
                        if (var2.Traits.HardOfHearing.isSet() && var10 < 0.7F) {
                            var10 = 0.7F;
                        }

                        float var11 = 2.0F;
                        if (var2.Traits.KeenHearing.isSet()) {
                            var11 += 3.0F;
                        }

                        if (var8 < var11 * (1.0F - var10) && !var2.Traits.Deaf.isSet()) {
                            var9 = -1.0F;
                        }
                    }

                    TestResults var19 = LosUtil.lineClearCached(this.getCell(), this.x, this.y, this.z, (int)var4.x, (int)var4.y, (int)var4.z, false, var1);
                    float var20 = -0.2F;
                    var20 = var20 - (var2.getStats().fatigue - 0.6F);
                    if (var20 > -0.2F) {
                        var20 = -0.2F;
                    }

                    if (var2.getStats().fatigue >= 1.0F) {
                        var20 -= 0.2F;
                    }

                    if (var2.getMoodles().getMoodleLevel(MoodleType.Panic) == 4) {
                        var20 -= 0.2F;
                    }

                    if (var20 < -0.9F) {
                        var20 = -0.9F;
                    }

                    if (var2.Traits.EagleEyed.isSet()) {
                        var20 += 0.2F;
                    }

                    if (var2 instanceof IsoPlayer && var2.getVehicle() != null) {
                        var20 = 1.0F;
                    }

                    if (!(var9 > var20) && var19 != TestResults.Blocked) {
                        var3.bCouldSee(true);
                        if (this.room == null || this.room.def == null || this.room.def.bExplored) {
                        }

                        byte var23 = 10;
                        if (var4.square != null && var4.square.getBuilding() == this.room.building) {
                            var23 = 50;
                        }

                        if ((!GameServer.bServer || !(var2 instanceof IsoPlayer) || !var2.isGhostMode())
                            && IsoUtils.DistanceManhatten(var4.x, var4.y, (float)this.x, (float)this.y) < (float)var23
                            && this.z == (int)var4.z) {
                            if (GameServer.bServer) {
                                DebugLog.log(DebugType.Zombie, "bExplored room=" + this.room.def.ID);
                            }

                            this.room.def.bExplored = true;
                            this.room.onSee();
                            this.room.seen = 0;
                        }
                    } else if (var19 == TestResults.Blocked) {
                        var3.bCouldSee(false);
                    } else {
                        var3.bCouldSee(true);
                    }

                    if (var9 > var20) {
                        var3.targetDarkMulti(var3.targetDarkMulti() * 0.85F);
                    }
                }
            }
        }
    }

    private TestResults DoDiagnalCheck(int var1, int var2, int var3, boolean var4) {
        TestResults var5 = this.testVisionAdjacent(var1, 0, var3, false, var4);
        if (var5 == TestResults.Blocked) {
            return TestResults.Blocked;
        } else {
            TestResults var6 = this.testVisionAdjacent(0, var2, var3, false, var4);
            if (var6 == TestResults.Blocked) {
                return TestResults.Blocked;
            } else if (var5 != TestResults.ClearThroughWindow && var6 != TestResults.ClearThroughWindow) {
                return this.testVisionAdjacent(var1, var2, var3, false, var4);
            } else {
                return TestResults.ClearThroughWindow;
            }
        }
    }

    boolean HasNoCharacters() {
        for (int var1 = 0; var1 < this.MovingObjects.size(); var1++) {
            if (this.MovingObjects.get(var1) instanceof IsoGameCharacter) {
                return false;
            }
        }

        for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
            if (this.SpecialObjects.get(var2) instanceof IsoBarricade) {
                return false;
            }
        }

        return true;
    }

    public IsoZombie getZombie() {
        for (int var1 = 0; var1 < this.MovingObjects.size(); var1++) {
            if (this.MovingObjects.get(var1) instanceof IsoZombie) {
                return (IsoZombie)this.MovingObjects.get(var1);
            }
        }

        return null;
    }

    public IsoPlayer getPlayer() {
        for (int var1 = 0; var1 < this.MovingObjects.size(); var1++) {
            if (this.MovingObjects.get(var1) instanceof IsoPlayer) {
                return (IsoPlayer)this.MovingObjects.get(var1);
            }
        }

        return null;
    }

    public static float getDarkStep() {
        return darkStep;
    }

    public static void setDarkStep(float var0) {
        darkStep = var0;
    }

    public static int getRecalcLightTime() {
        return RecalcLightTime;
    }

    public static void setRecalcLightTime(int var0) {
        RecalcLightTime = var0;
    }

    public static int getLightcache() {
        return lightcache;
    }

    public static void setLightcache(int var0) {
        lightcache = var0;
    }

    public boolean isCouldSee(int var1) {
        return this.lighting[var1].bCouldSee();
    }

    public void setCouldSee(int var1, boolean var2) {
        this.lighting[var1].bCouldSee(var2);
    }

    public boolean isCanSee(int var1) {
        return this.lighting[var1].bCanSee();
    }

    public void setCanSee(int var1, boolean var2) {
        this.lighting[var1].bCanSee(var2);
    }

    public IsoCell getCell() {
        return IsoWorld.instance.CurrentCell;
    }

    public IsoGridSquare getE() {
        return this.e;
    }

    public void setE(IsoGridSquare var1) {
        this.e = var1;
    }

    public ArrayList<Float> getLightInfluenceB() {
        return this.LightInfluenceB;
    }

    public void setLightInfluenceB(ArrayList<Float> var1) {
        this.LightInfluenceB = var1;
    }

    public ArrayList<Float> getLightInfluenceG() {
        return this.LightInfluenceG;
    }

    public void setLightInfluenceG(ArrayList<Float> var1) {
        this.LightInfluenceG = var1;
    }

    public ArrayList<Float> getLightInfluenceR() {
        return this.LightInfluenceR;
    }

    public void setLightInfluenceR(ArrayList<Float> var1) {
        this.LightInfluenceR = var1;
    }

    public ArrayList<IsoMovingObject> getStaticMovingObjects() {
        return this.StaticMovingObjects;
    }

    public ArrayList<IsoMovingObject> getMovingObjects() {
        return this.MovingObjects;
    }

    public IsoGridSquare getN() {
        return this.n;
    }

    public void setN(IsoGridSquare var1) {
        this.n = var1;
    }

    public PZArrayList<IsoObject> getObjects() {
        return this.Objects;
    }

    public PropertyContainer getProperties() {
        return this.Properties;
    }

    public IsoRoom getRoom() {
        if (this.roomID == -1) {
            return null;
        } else {
            return this.room;
        }
    }

    public void setRoom(IsoRoom var1) {
        this.room = var1;
    }

    public IsoBuilding getBuilding() {
        IsoRoom var1 = this.getRoom();
        if (var1 != null) {
            return var1.getBuilding();
        } else {
            return null;
        }
    }

    public IsoGridSquare getS() {
        return this.s;
    }

    public void setS(IsoGridSquare var1) {
        this.s = var1;
    }

    public ArrayList<IsoObject> getSpecialObjects() {
        return this.SpecialObjects;
    }

    public IsoGridSquare getW() {
        return this.w;
    }

    public void setW(IsoGridSquare var1) {
        this.w = var1;
    }

    public float getLampostTotalR() {
        return this.lighting[0].lampostTotalR();
    }

    public void setLampostTotalR(float var1) {
        this.lighting[0].lampostTotalR(var1);
    }

    public float getLampostTotalG() {
        return this.lighting[0].lampostTotalG();
    }

    public void setLampostTotalG(float var1) {
        this.lighting[0].lampostTotalG(var1);
    }

    public float getLampostTotalB() {
        return this.lighting[0].lampostTotalB();
    }

    public void setLampostTotalB(float var1) {
        this.lighting[0].lampostTotalB(var1);
    }

    public boolean isSeen(int var1) {
        return this.lighting[var1].bSeen();
    }

    public void setIsSeen(int var1, boolean var2) {
        this.lighting[var1].bSeen(var2);
    }

    public float getDarkMulti(int var1) {
        return this.lighting[var1].darkMulti();
    }

    public void setDarkMulti(int var1, float var2) {
        this.lighting[var1].darkMulti(var2);
    }

    public float getTargetDarkMulti(int var1) {
        return this.lighting[var1].targetDarkMulti();
    }

    public void setTargetDarkMulti(int var1, float var2) {
        this.lighting[var1].targetDarkMulti(var2);
    }

    public void setX(int var1) {
        this.x = var1;
        this.CachedScreenValue = -1;
    }

    public void setY(int var1) {
        this.y = var1;
        this.CachedScreenValue = -1;
    }

    public void setZ(int var1) {
        this.z = var1;
        this.CachedScreenValue = -1;
    }

    public ArrayList<IsoGameCharacter> getDeferedCharacters() {
        return this.DeferedCharacters;
    }

    public void addDeferredCharacter(IsoGameCharacter var1) {
        if (this.DeferredCharacterTick != this.getCell().DeferredCharacterTick) {
            if (!this.DeferedCharacters.isEmpty()) {
                this.DeferedCharacters.clear();
            }

            this.DeferredCharacterTick = this.getCell().DeferredCharacterTick;
        }

        this.DeferedCharacters.add(var1);
    }

    public boolean isCacheIsFree() {
        return this.CacheIsFree;
    }

    public void setCacheIsFree(boolean var1) {
        this.CacheIsFree = var1;
    }

    public boolean isCachedIsFree() {
        return this.CachedIsFree;
    }

    public void setCachedIsFree(boolean var1) {
        this.CachedIsFree = var1;
    }

    public static boolean isbDoSlowPathfinding() {
        return bDoSlowPathfinding;
    }

    public static void setbDoSlowPathfinding(boolean var0) {
        bDoSlowPathfinding = var0;
    }

    public boolean isSolidFloorCached() {
        return this.SolidFloorCached;
    }

    public void setSolidFloorCached(boolean var1) {
        this.SolidFloorCached = var1;
    }

    public boolean isSolidFloor() {
        return this.SolidFloor;
    }

    public void setSolidFloor(boolean var1) {
        this.SolidFloor = var1;
    }

    public static ColorInfo getDefColorInfo() {
        return defColorInfo;
    }

    public boolean isOutside() {
        return this.Properties.Is(IsoFlagType.exterior);
    }

    public boolean HasPushable() {
        int var1 = this.MovingObjects.size();

        for (int var2 = 0; var2 < var1; var2++) {
            if (this.MovingObjects.get(var2) instanceof IsoPushableObject) {
                return true;
            }
        }

        return false;
    }

    public void setRoomID(int var1) {
        this.roomID = var1;
        if (var1 != -1) {
            this.getProperties().UnSet(IsoFlagType.exterior);
            this.room = this.chunk.getRoom(var1);
        }
    }

    public int getRoomID() {
        return this.roomID;
    }

    public boolean getCanSee(int var1) {
        return this.lighting[var1].bCanSee();
    }

    public boolean getSeen(int var1) {
        return this.lighting[var1].bSeen();
    }

    public IsoChunk getChunk() {
        return this.chunk;
    }

    public IsoObject getDoorOrWindow(boolean var1) {
        for (int var2 = this.SpecialObjects.size() - 1; var2 >= 0; var2--) {
            IsoObject var3 = this.SpecialObjects.get(var2);
            if (var3 instanceof IsoDoor && ((IsoDoor)var3).north == var1) {
                return var3;
            }

            if (var3 instanceof IsoThumpable && ((IsoThumpable)var3).north == var1 && (((IsoThumpable)var3).isDoor() || ((IsoThumpable)var3).isWindow())) {
                return var3;
            }

            if (var3 instanceof IsoWindow && ((IsoWindow)var3).north == var1) {
                return var3;
            }
        }

        return null;
    }

    public IsoObject getDoorOrWindowOrWindowFrame(IsoDirections var1, boolean var2) {
        for (int var3 = this.Objects.size() - 1; var3 >= 0; var3--) {
            IsoObject var4 = (IsoObject)this.Objects.get(var3);
            IsoDoor var5 = (IsoDoor)Type.tryCastTo(var4, IsoDoor.class);
            IsoThumpable var6 = (IsoThumpable)Type.tryCastTo(var4, IsoThumpable.class);
            IsoWindow var7 = (IsoWindow)Type.tryCastTo(var4, IsoWindow.class);
            if (var5 != null && var5.getSpriteEdge(var2) == var1) {
                return var4;
            }

            if (var6 != null && var6.getSpriteEdge(var2) == var1) {
                return var4;
            }

            if (var7 != null) {
                if (var7.north && var1 == IsoDirections.N) {
                    return var4;
                }

                if (!var7.north && var1 == IsoDirections.W) {
                    return var4;
                }
            }

            if (IsoWindowFrame.isWindowFrame(var4)) {
                if (IsoWindowFrame.isWindowFrame(var4, true) && var1 == IsoDirections.N) {
                    return var4;
                }

                if (IsoWindowFrame.isWindowFrame(var4, false) && var1 == IsoDirections.W) {
                    return var4;
                }
            }
        }

        return null;
    }

    public IsoObject getOpenDoor(IsoDirections var1) {
        for (int var2 = 0; var2 < this.SpecialObjects.size(); var2++) {
            IsoObject var3 = this.SpecialObjects.get(var2);
            IsoDoor var4 = (IsoDoor)Type.tryCastTo(var3, IsoDoor.class);
            IsoThumpable var5 = (IsoThumpable)Type.tryCastTo(var3, IsoThumpable.class);
            if (var4 != null && var4.open && var4.getSpriteEdge(false) == var1) {
                return var4;
            }

            if (var5 != null && var5.open && var5.getSpriteEdge(false) == var1) {
                return var5;
            }
        }

        return null;
    }

    public void removeWorldObject(IsoWorldInventoryObject var1) {
        if (var1 != null) {
            var1.removeFromWorld();
            var1.removeFromSquare();
        }
    }

    public void removeAllWorldObjects() {
        for (int var1 = 0; var1 < this.getWorldObjects().size(); var1++) {
            IsoObject var2 = (IsoObject)this.getWorldObjects().get(var1);
            var2.removeFromWorld();
            var2.removeFromSquare();
            var1--;
        }
    }

    public ArrayList<IsoWorldInventoryObject> getWorldObjects() {
        return this.WorldObjects;
    }

    public PZArrayList<IsoObject> getLocalTemporaryObjects() {
        return this.localTemporaryObjects;
    }

    public KahluaTable getModData() {
        if (this.table == null) {
            this.table = LuaManager.platform.newTable();
        }

        return this.table;
    }

    public boolean hasModData() {
        return this.table != null && !this.table.isEmpty();
    }

    public ZomboidBitFlag getHasTypes() {
        return this.hasTypes;
    }

    public void setVertLight(int var1, int var2, int var3) {
        this.lighting[var3].lightverts(var1, var2);
    }

    public int getVertLight(int var1, int var2) {
        return this.lighting[var2].lightverts(var1);
    }

    public void setRainDrop(IsoRaindrop var1) {
        this.RainDrop = var1;
    }

    public IsoRaindrop getRainDrop() {
        return this.RainDrop;
    }

    public void setRainSplash(IsoRainSplash var1) {
        this.RainSplash = var1;
    }

    public IsoRainSplash getRainSplash() {
        return this.RainSplash;
    }

    public Zone getZone() {
        return this.zone;
    }

    public String getZoneType() {
        if (this.zone != null) {
            return this.zone.getType();
        } else {
            return null;
        }
    }

    public boolean isOverlayDone() {
        return this.overlayDone;
    }

    public void setOverlayDone(boolean var1) {
        this.overlayDone = var1;
    }

    public Square getErosionData() {
        if (this.erosion == null) {
            this.erosion = new Square();
        }

        return this.erosion;
    }

    public void disableErosion() {
        Square var1 = this.getErosionData();
        if (var1 != null && !var1.doNothing) {
            var1.doNothing = true;
        }
    }

    public void removeErosionObject(String var1) {
        if (this.erosion != null) {
            if ("WallVines".equals(var1)) {
                for (int var2 = 0; var2 < this.erosion.regions.size(); var2++) {
                    Data var3 = (Data)this.erosion.regions.get(var2);
                    if (var3.regionID == 2 && var3.categoryID == 0) {
                        this.erosion.regions.remove(var2);
                        break;
                    }
                }
            }
        }
    }

    public void syncIsoTrap(HandWeapon var1) {
        ByteBufferWriter var2 = GameClient.connection.startPacket();
        PacketType.AddExplosiveTrap.doPacket(var2);
        var2.putInt(this.getX());
        var2.putInt(this.getY());
        var2.putInt(this.getZ());

        try {
            var1.saveWithSize(var2.bb, false);
        } catch (Exception var4) {
            ExceptionLogger.logException(var4);
        }
    }

    public void drawCircleExplosion(int var1, IsoTrap var2, ExplosionMode var3) {
        if (var1 > 15) {
            var1 = 15;
        }

        for (int var4 = this.getX() - var1; var4 <= this.getX() + var1; var4++) {
            for (int var5 = this.getY() - var1; var5 <= this.getY() + var1; var5++) {
                if (!(IsoUtils.DistanceTo((float)var4 + 0.5F, (float)var5 + 0.5F, (float)this.getX() + 0.5F, (float)this.getY() + 0.5F) > (float)var1)) {
                    TestResults var6 = LosUtil.lineClear(this.getCell(), (int)var2.getX(), (int)var2.getY(), (int)var2.getZ(), var4, var5, this.z, false);
                    if (var6 != TestResults.Blocked && var6 != TestResults.ClearThroughClosedDoor) {
                        IsoGridSquare var7 = this.getCell().getGridSquare(var4, var5, this.getZ());
                        if (var7 != null && NonPvpZone.getNonPvpZone(var7.getX(), var7.getY()) == null) {
                            if (var3 == ExplosionMode.Smoke) {
                                if (!GameClient.bClient && Rand.Next(2) == 0) {
                                    IsoFireManager.StartSmoke(this.getCell(), var7, true, 40, 0);
                                }

                                var7.smoke();
                            }

                            if (var3 == ExplosionMode.Explosion) {
                                if (!GameClient.bClient && var2.getExplosionPower() > 0 && Rand.Next(80 - var2.getExplosionPower()) <= 0) {
                                    var7.Burn();
                                }

                                var7.explosion(var2);
                                if (!GameClient.bClient && var2.getExplosionPower() > 0 && Rand.Next(100 - var2.getExplosionPower()) == 0) {
                                    IsoFireManager.StartFire(this.getCell(), var7, true, 20);
                                }
                            }

                            if (var3 == ExplosionMode.Fire && !GameClient.bClient && Rand.Next(100 - var2.getFirePower()) == 0) {
                                IsoFireManager.StartFire(this.getCell(), var7, true, 40);
                            }

                            if (var3 == ExplosionMode.Sensor) {
                                var7.setTrapPositionX(this.getX());
                                var7.setTrapPositionY(this.getY());
                                var7.setTrapPositionZ(this.getZ());
                            }
                        }
                    }
                }
            }
        }
    }

    public void explosion(IsoTrap var1) {
        // $VF: Couldn't be decompiled
        // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
        // java.lang.IllegalStateException: No successor exists for {Do}:44
        //   at org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.getFirstSuccessor(Statement.java:834)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:276)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:478)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:257)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:458)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.flattenStatement(FlattenStatementsHelper.java:474)
        //   at org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper.buildDirectGraph(FlattenStatementsHelper.java:43)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:151)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarDefinitionHelper.<init>(VarDefinitionHelper.java:52)
        //   at org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor.setVarDefinitions(VarProcessor.java:52)
        //   at org.jetbrains.java.decompiler.main.rels.MethodProcessor.codeToJava(MethodProcessor.java:475)
        //
        // Bytecode:
        // 000: getstatic zombie/network/GameServer.bServer Z
        // 003: ifeq 00e
        // 006: aload 1
        // 007: invokevirtual zombie/iso/objects/IsoTrap.isInstantExplosion ()Z
        // 00a: ifeq 00e
        // 00d: return
        // 00e: bipush 0
        // 00f: istore 2
        // 010: iload 2
        // 011: aload 0
        // 012: invokevirtual zombie/iso/IsoGridSquare.getMovingObjects ()Ljava/util/ArrayList;
        // 015: invokevirtual java/util/ArrayList.size ()I
        // 018: if_icmpge 101
        // 01b: aload 0
        // 01c: invokevirtual zombie/iso/IsoGridSquare.getMovingObjects ()Ljava/util/ArrayList;
        // 01f: iload 2
        // 020: invokevirtual java/util/ArrayList.get (I)Ljava/lang/Object;
        // 023: checkcast zombie/iso/IsoMovingObject
        // 026: astore 3
        // 027: aload 3
        // 028: instanceof zombie/characters/IsoGameCharacter
        // 02b: ifeq 0fb
        // 02e: getstatic zombie/network/GameServer.bServer Z
        // 031: ifne 045
        // 034: aload 3
        // 035: instanceof zombie/characters/IsoZombie
        // 038: ifeq 045
        // 03b: aload 3
        // 03c: checkcast zombie/characters/IsoZombie
        // 03f: invokevirtual zombie/characters/IsoZombie.isLocal ()Z
        // 042: ifeq 0ca
        // 045: aload 1
        // 046: invokevirtual zombie/iso/objects/IsoTrap.getExplosionPower ()I
        // 049: bipush 80
        // 04b: invokestatic java/lang/Math.min (II)I
        // 04e: istore 4
        // 050: aload 3
        // 051: ldc_w "Base.Axe"
        // 054: invokestatic zombie/inventory/InventoryItemFactory.CreateItem (Ljava/lang/String;)Lzombie/inventory/InventoryItem;
        // 057: checkcast zombie/inventory/types/HandWeapon
        // 05a: getstatic zombie/iso/IsoWorld.instance Lzombie/iso/IsoWorld;
        // 05d: getfield zombie/iso/IsoWorld.CurrentCell Lzombie/iso/IsoCell;
        // 060: invokevirtual zombie/iso/IsoCell.getFakeZombieForHit ()Lzombie/characters/IsoZombie;
        // 063: iload 4
        // 065: i2f
        // 066: ldc_w 30.0
        // 069: fdiv
        // 06a: iload 4
        // 06c: i2f
        // 06d: ldc_w 30.0
        // 070: fdiv
        // 071: fconst_2
        // 072: fmul
        // 073: invokestatic zombie/core/Rand.Next (FF)F
        // 076: aload 1
        // 077: invokevirtual zombie/iso/objects/IsoTrap.getExtraDamage ()F
        // 07a: fadd
        // 07b: bipush 0
        // 07c: fconst_1
        // 07d: invokevirtual zombie/iso/IsoMovingObject.Hit (Lzombie/inventory/types/HandWeapon;Lzombie/characters/IsoGameCharacter;FZF)F
        // 080: pop
        // 081: aload 1
        // 082: invokevirtual zombie/iso/objects/IsoTrap.getExplosionPower ()I
        // 085: ifle 0ca
        // 088: aload 3
        // 089: instanceof zombie/characters/IsoZombie
        // 08c: ifne 093
        // 08f: bipush 1
        // 090: goto 094
        // 093: bipush 0
        // 094: istore 5
        // 096: iload 5
        // 098: ifeq 0ca
        // 09b: bipush 0
        // 09c: istore 5
        // 09e: aload 3
        // 09f: checkcast zombie/characters/IsoGameCharacter
        // 0a2: invokevirtual zombie/characters/IsoGameCharacter.getBodyDamage ()Lzombie/characters/BodyDamage/BodyDamage;
        // 0a5: bipush 15
        // 0a7: invokestatic zombie/core/Rand.Next (I)I
        // 0aa: invokestatic zombie/characters/BodyDamage/BodyPartType.FromIndex (I)Lzombie/characters/BodyDamage/BodyPartType;
        // 0ad: invokevirtual zombie/characters/BodyDamage/BodyDamage.getBodyPart (Lzombie/characters/BodyDamage/BodyPartType;)Lzombie/characters/BodyDamage/BodyPart;
        // 0b0: astore 6
        // 0b2: aload 6
        // 0b4: invokevirtual zombie/characters/BodyDamage/BodyPart.setBurned ()V
        // 0b7: bipush 100
        // 0b9: iload 4
        // 0bb: isub
        // 0bc: bipush 2
        // 0bd: idiv
        // 0be: invokestatic zombie/core/Rand.Next (I)I
        // 0c1: ifne 0c7
        // 0c4: bipush 1
        // 0c5: istore 5
        // 0c7: goto 096
        // 0ca: getstatic zombie/network/GameClient.bClient Z
        // 0cd: ifeq 0fb
        // 0d0: aload 3
        // 0d1: instanceof zombie/characters/IsoZombie
        // 0d4: ifeq 0fb
        // 0d7: aload 3
        // 0d8: checkcast zombie/characters/IsoZombie
        // 0db: invokevirtual zombie/characters/IsoZombie.isRemoteZombie ()Z
        // 0de: ifeq 0fb
        // 0e1: aload 3
        // 0e2: ldc_w "Base.Axe"
        // 0e5: invokestatic zombie/inventory/InventoryItemFactory.CreateItem (Ljava/lang/String;)Lzombie/inventory/InventoryItem;
        // 0e8: checkcast zombie/inventory/types/HandWeapon
        // 0eb: getstatic zombie/iso/IsoWorld.instance Lzombie/iso/IsoWorld;
        // 0ee: getfield zombie/iso/IsoWorld.CurrentCell Lzombie/iso/IsoCell;
        // 0f1: invokevirtual zombie/iso/IsoCell.getFakeZombieForHit ()Lzombie/characters/IsoZombie;
        // 0f4: fconst_0
        // 0f5: bipush 1
        // 0f6: fconst_0
        // 0f7: invokevirtual zombie/iso/IsoMovingObject.Hit (Lzombie/inventory/types/HandWeapon;Lzombie/characters/IsoGameCharacter;FZF)F
        // 0fa: pop
        // 0fb: iinc 2 1
        // 0fe: goto 010
        // 101: return
    }

    public void smoke() {
        for (int var1 = 0; var1 < this.getMovingObjects().size(); var1++) {
            IsoMovingObject var2 = this.getMovingObjects().get(var1);
            if (var2 instanceof IsoZombie) {
                ((IsoZombie)var2).setTarget(null);
                ((IsoZombie)var2).changeState(ZombieIdleState.instance());
            }
        }
    }

    public void explodeTrap() {
        IsoGridSquare var1 = this.getCell().getGridSquare(this.getTrapPositionX(), this.getTrapPositionY(), this.getTrapPositionZ());
        if (var1 != null) {
            for (int var2 = 0; var2 < var1.getObjects().size(); var2++) {
                IsoObject var3 = (IsoObject)var1.getObjects().get(var2);
                if (var3 instanceof IsoTrap var4) {
                    var4.triggerExplosion(false);
                    IsoGridSquare var5 = null;
                    int var6 = var4.getSensorRange();

                    for (int var7 = var1.getX() - var6; var7 <= var1.getX() + var6; var7++) {
                        for (int var8 = var1.getY() - var6; var8 <= var1.getY() + var6; var8++) {
                            if (IsoUtils.DistanceTo((float)var7 + 0.5F, (float)var8 + 0.5F, (float)var1.getX() + 0.5F, (float)var1.getY() + 0.5F)
                                <= (float)var6) {
                                var5 = this.getCell().getGridSquare(var7, var8, this.getZ());
                                if (var5 != null) {
                                    var5.setTrapPositionX(-1);
                                    var5.setTrapPositionY(-1);
                                    var5.setTrapPositionZ(-1);
                                }
                            }
                        }
                    }

                    return;
                }
            }
        }
    }

    public int getTrapPositionX() {
        return this.trapPositionX;
    }

    public void setTrapPositionX(int var1) {
        this.trapPositionX = var1;
    }

    public int getTrapPositionY() {
        return this.trapPositionY;
    }

    public void setTrapPositionY(int var1) {
        this.trapPositionY = var1;
    }

    public int getTrapPositionZ() {
        return this.trapPositionZ;
    }

    public void setTrapPositionZ(int var1) {
        this.trapPositionZ = var1;
    }

    public boolean haveElectricity() {
        if ((this.chunk == null || !this.chunk.bLoaded) && this.haveElectricity) {
            return true;
        } else if (!SandboxOptions.getInstance().AllowExteriorGenerator.getValue() && this.Is(IsoFlagType.exterior)) {
            return false;
        } else {
            return this.chunk != null && this.chunk.isGeneratorPoweringSquare(this.x, this.y, this.z);
        }
    }

    public void setHaveElectricity(boolean var1) {
        if (!var1) {
            this.haveElectricity = false;
        }

        if (this.getObjects() != null) {
            for (int var2 = 0; var2 < this.getObjects().size(); var2++) {
                if (this.getObjects().get(var2) instanceof IsoLightSwitch) {
                    ((IsoLightSwitch)this.getObjects().get(var2)).update();
                }
            }
        }
    }

    public IsoGenerator getGenerator() {
        if (this.getSpecialObjects() != null) {
            for (int var1 = 0; var1 < this.getSpecialObjects().size(); var1++) {
                if (this.getSpecialObjects().get(var1) instanceof IsoGenerator) {
                    return (IsoGenerator)this.getSpecialObjects().get(var1);
                }
            }
        }

        return null;
    }

    public void stopFire() {
        IsoFireManager.RemoveAllOn(this);
        this.getProperties().Set(IsoFlagType.burntOut);
        this.getProperties().UnSet(IsoFlagType.burning);
        this.burntOut = true;
    }

    public void transmitStopFire() {
        if (GameClient.bClient) {
            GameClient.sendStopFire(this);
        }
    }

    public long playSound(String var1) {
        BaseSoundEmitter var2 = IsoWorld.instance.getFreeEmitter((float)this.x + 0.5F, (float)this.y + 0.5F, (float)this.z);
        return var2.playSound(var1);
    }

    @Deprecated
    public long playSound(String var1, boolean var2) {
        BaseSoundEmitter var3 = IsoWorld.instance.getFreeEmitter((float)this.x + 0.5F, (float)this.y + 0.5F, (float)this.z);
        return var3.playSound(var1, var2);
    }

    public void FixStackableObjects() {
        IsoObject var1 = null;

        for (int var2 = 0; var2 < this.Objects.size(); var2++) {
            IsoObject var3 = (IsoObject)this.Objects.get(var2);
            if (!(var3 instanceof IsoWorldInventoryObject) && var3.sprite != null) {
                PropertyContainer var4 = var3.sprite.getProperties();
                if (var4.getStackReplaceTileOffset() != 0) {
                    var3.sprite = IsoSprite.getSprite(IsoSpriteManager.instance, var3.sprite.ID + var4.getStackReplaceTileOffset());
                    if (var3.sprite == null) {
                        continue;
                    }

                    var4 = var3.sprite.getProperties();
                }

                if (!var4.isTable() && !var4.isTableTop()) {
                }

                float var5 = var4.isSurfaceOffset() ? (float)var4.getSurface() : 0.0F;
                if (var1 != null) {
                    var3.setRenderYOffset(var1.getRenderYOffset() + var1.getSurfaceOffset() - var5);
                } else {
                    var3.setRenderYOffset(0.0F - var5);
                }
            }
        }
    }

    public void fixPlacedItemRenderOffsets() {
        IsoObject[] var1 = (IsoObject[])this.Objects.getElements();
        int var2 = this.Objects.size();
        int var3 = 0;

        for (int var4 = 0; var4 < var2; var4++) {
            IsoObject var5 = var1[var4];
            int var6 = PZMath.roundToInt(var5.getSurfaceOffsetNoTable());
            if (!((float)var6 <= 0.0F) && !PZArrayUtil.contains(SURFACE_OFFSETS, var3, var6)) {
                int var10001 = var3;
                var3++;
                SURFACE_OFFSETS[var10001] = var6;
            }
        }

        if (var3 == 0) {
            int var13 = var3;
            var3++;
            SURFACE_OFFSETS[var13] = 0;
        }

        for (int var10 = 0; var10 < var2; var10++) {
            IsoObject var11 = var1[var10];
            IsoWorldInventoryObject var12 = (IsoWorldInventoryObject)Type.tryCastTo(var11, IsoWorldInventoryObject.class);
            if (var12 == null) {
                continue;
            }

            int var7 = PZMath.roundToInt(var12.zoff * 96.0F);
            int var8 = 0;

            for (int var9 = 0; var9 < var3; var9++) {
                if (var7 <= SURFACE_OFFSETS[var9]) {
                    var8 = SURFACE_OFFSETS[var9];
                    break;
                }

                var8 = SURFACE_OFFSETS[var9];
                if (var9 < var3 - 1 && var7 < SURFACE_OFFSETS[var9 + 1]) {
                    break;
                }
            }

            var12.zoff = (float)var8 / 96.0F;
        }
    }

    public BaseVehicle getVehicleContainer() {
        int var1 = (int)(((float)this.x - 4.0F) / 10.0F);
        int var2 = (int)(((float)this.y - 4.0F) / 10.0F);
        int var3 = (int)Math.ceil((double)(((float)this.x + 4.0F) / 10.0F));
        int var4 = (int)Math.ceil((double)(((float)this.y + 4.0F) / 10.0F));

        for (int var5 = var2; var5 < var4; var5++) {
            for (int var6 = var1; var6 < var3; var6++) {
                IsoChunk var7 = GameServer.bServer ? ServerMap.instance.getChunk(var6, var5) : IsoWorld.instance.CurrentCell.getChunk(var6, var5);
                if (var7 == null) {
                    continue;
                }

                for (int var8 = 0; var8 < var7.vehicles.size(); var8++) {
                    BaseVehicle var9 = (BaseVehicle)var7.vehicles.get(var8);
                    if (var9.isIntersectingSquare(this.x, this.y, this.z)) {
                        return var9;
                    }
                }
            }
        }

        return null;
    }

    public boolean isVehicleIntersecting() {
        int var1 = (int)(((float)this.x - 4.0F) / 10.0F);
        int var2 = (int)(((float)this.y - 4.0F) / 10.0F);
        int var3 = (int)Math.ceil((double)(((float)this.x + 4.0F) / 10.0F));
        int var4 = (int)Math.ceil((double)(((float)this.y + 4.0F) / 10.0F));

        for (int var5 = var2; var5 < var4; var5++) {
            for (int var6 = var1; var6 < var3; var6++) {
                IsoChunk var7 = GameServer.bServer ? ServerMap.instance.getChunk(var6, var5) : IsoWorld.instance.CurrentCell.getChunk(var6, var5);
                if (var7 == null) {
                    continue;
                }

                for (int var8 = 0; var8 < var7.vehicles.size(); var8++) {
                    BaseVehicle var9 = (BaseVehicle)var7.vehicles.get(var8);
                    if (var9.isIntersectingSquare(this.x, this.y, this.z)) {
                        return true;
                    }
                }
            }
        }

        return false;
    }

    public IsoCompost getCompost() {
        if (this.getSpecialObjects() != null) {
            for (int var1 = 0; var1 < this.getSpecialObjects().size(); var1++) {
                if (this.getSpecialObjects().get(var1) instanceof IsoCompost) {
                    return (IsoCompost)this.getSpecialObjects().get(var1);
                }
            }
        }

        return null;
    }

    public void setIsoWorldRegion(IsoWorldRegion var1) {
        this.hasSetIsoWorldRegion = var1 != null;
        this.isoWorldRegion = var1;
    }

    public IWorldRegion getIsoWorldRegion() {
        if (GameServer.bServer) {
            return IsoRegions.getIsoWorldRegion(this.x, this.y, this.z);
        } else {
            if (!this.hasSetIsoWorldRegion) {
                this.isoWorldRegion = IsoRegions.getIsoWorldRegion(this.x, this.y, this.z);
                this.hasSetIsoWorldRegion = true;
            }

            return this.isoWorldRegion;
        }
    }

    public void ResetIsoWorldRegion() {
        this.isoWorldRegion = null;
        this.hasSetIsoWorldRegion = false;
    }

    public boolean isInARoom() {
        return this.getRoom() != null || this.getIsoWorldRegion() != null && this.getIsoWorldRegion().isPlayerRoom();
    }

    public int getRoomSize() {
        if (this.getRoom() != null) {
            return this.getRoom().getSquares().size();
        } else if (this.getIsoWorldRegion() != null && this.getIsoWorldRegion().isPlayerRoom()) {
            return this.getIsoWorldRegion().getSquareSize();
        } else {
            return -1;
        }
    }

    public int getWallType() {
        byte var1 = 0;
        if (this.getProperties().Is(IsoFlagType.WallN)) {
            var1 |= 1;
        }

        if (this.getProperties().Is(IsoFlagType.WallW)) {
            var1 |= 4;
        }

        if (this.getProperties().Is(IsoFlagType.WallNW)) {
            var1 |= 5;
        }

        IsoGridSquare var2 = this.nav[IsoDirections.E.index()];
        label31:
        if (var2 != null) {
            if (!var2.getProperties().Is(IsoFlagType.WallW) && !var2.getProperties().Is(IsoFlagType.WallNW)) {
                break label31;
            }

            var1 |= 8;
        }

        IsoGridSquare var3 = this.nav[IsoDirections.S.index()];
        if (var3 != null) {
            if (!var3.getProperties().Is(IsoFlagType.WallN) && !var3.getProperties().Is(IsoFlagType.WallNW)) {
                return var1;
            }

            var1 |= 2;
        }

        return var1;
    }

    public int getPuddlesDir() {
        byte var1 = PuddlesDirection.PUDDLES_DIR_ALL;
        if (this.isInARoom()) {
            return PuddlesDirection.PUDDLES_DIR_NONE;
        } else {
            for (int var2 = 0; var2 < this.getObjects().size(); var2++) {
                IsoObject var3 = (IsoObject)this.getObjects().get(var2);
                if (var3.AttachedAnimSprite == null) {
                    continue;
                }

                for (int var4 = 0; var4 < var3.AttachedAnimSprite.size(); var4++) {
                    IsoSprite var5 = ((IsoSpriteInstance)var3.AttachedAnimSprite.get(var4)).parentSprite;
                    if (var5.name != null) {
                        if (!var5.name.equals("street_trafficlines_01_2")
                            && !var5.name.equals("street_trafficlines_01_6")
                            && !var5.name.equals("street_trafficlines_01_22")
                            && !var5.name.equals("street_trafficlines_01_32")) {
                        }

                        var1 = PuddlesDirection.PUDDLES_DIR_NW;
                    }
                }
            }

            return var1;
        }
    }

    public boolean haveFire() {
        int var1 = this.Objects.size();
        IsoObject[] var2 = (IsoObject[])this.Objects.getElements();

        for (int var3 = 0; var3 < var1; var3++) {
            IsoObject var4 = var2[var3];
            if (var4 instanceof IsoFire) {
                return true;
            }
        }

        return false;
    }

    public IsoBuilding getRoofHideBuilding() {
        return this.roofHideBuilding;
    }

    public IsoGridSquare getAdjacentSquare(IsoDirections var1) {
        return this.nav[var1.index()];
    }

    // $VF: Unable to simplify switch on enum
    // Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)
    public IsoGridSquare getAdjacentPathSquare(IsoDirections var1) {
        switch (1.$SwitchMap$zombie$iso$IsoDirections[var1.ordinal()]) {
            case 1:
                return this.nw;
            case 2:
                return this.n;
            case 3:
                return this.ne;
            case 4:
                return this.w;
            case 5:
                return this.e;
            case 6:
                return this.sw;
            case 7:
                return this.s;
            case 8:
                return this.se;
            default:
                return null;
        }
    }

    public float getApparentZ(float var1, float var2) {
        var1 = PZMath.clamp(var1, 0.0F, 1.0F);
        var2 = PZMath.clamp(var2, 0.0F, 1.0F);
        if (this.Has(IsoObjectType.stairsTN)) {
            return (float)this.getZ() + PZMath.lerp(0.6666F, 1.0F, 1.0F - var2);
        } else if (this.Has(IsoObjectType.stairsTW)) {
            return (float)this.getZ() + PZMath.lerp(0.6666F, 1.0F, 1.0F - var1);
        } else if (this.Has(IsoObjectType.stairsMN)) {
            return (float)this.getZ() + PZMath.lerp(0.3333F, 0.6666F, 1.0F - var2);
        } else if (this.Has(IsoObjectType.stairsMW)) {
            return (float)this.getZ() + PZMath.lerp(0.3333F, 0.6666F, 1.0F - var1);
        } else if (this.Has(IsoObjectType.stairsBN)) {
            return (float)this.getZ() + PZMath.lerp(0.01F, 0.3333F, 1.0F - var2);
        } else if (this.Has(IsoObjectType.stairsBW)) {
            return (float)this.getZ() + PZMath.lerp(0.01F, 0.3333F, 1.0F - var1);
        } else {
            return (float)this.getZ();
        }
    }

    public float getTotalWeightOfItemsOnFloor() {
        float var1 = 0.0F;

        for (int var2 = 0; var2 < this.WorldObjects.size(); var2++) {
            InventoryItem var3 = this.WorldObjects.get(var2).getItem();
            if (var3 != null) {
                var1 += var3.getUnequippedWeight();
            }
        }

        return var1;
    }

    public boolean getCollideMatrix(int var1, int var2, int var3) {
        return getMatrixBit(this.collideMatrix, var1 + 1, var2 + 1, var3 + 1);
    }

    public boolean getPathMatrix(int var1, int var2, int var3) {
        return getMatrixBit(this.pathMatrix, var1 + 1, var2 + 1, var3 + 1);
    }

    public boolean getVisionMatrix(int var1, int var2, int var3) {
        return getMatrixBit(this.visionMatrix, var1 + 1, var2 + 1, var3 + 1);
    }

    public void checkRoomSeen(int var1) {
        IsoRoom var2 = this.getRoom();
        if (var2 != null && var2.def != null && !var2.def.bExplored) {
            IsoPlayer var3 = IsoPlayer.players[var1];
            if (var3 != null) {
                if (this.z == (int)var3.z) {
                    byte var4 = 10;
                    if (var3.getBuilding() == var2.building) {
                        var4 = 50;
                    }

                    if (IsoUtils.DistanceToSquared(var3.x, var3.y, (float)this.x + 0.5F, (float)this.y + 0.5F) < (float)(var4 * var4)) {
                        var2.def.bExplored = true;
                        var2.onSee();
                        var2.seen = 0;
                    }
                }
            }
        }
    }

    public boolean hasFlies() {
        return this.bHasFlies;
    }

    public void setHasFlies(boolean var1) {
        this.bHasFlies = var1;
    }

    public float getLightLevel(int var1) {
        return (this.lighting[var1].lightInfo().r + this.lighting[var1].lightInfo().g + this.lighting[var1].lightInfo().b) / 3.0F;
    }
}
