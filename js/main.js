/**
 * 墨水屏控制台主模块
 * 原始版本功能完全保留，增量增加：
 * - 自动识别 Web 协议（6275...）和 APP 协议（0000ff01...）
 * - APP 模式下的图片发送（支持 LZ77 压缩、A/B 面选择）
 * - 不影响原有任何功能，新旧模式自动切换
 * - 新增：根据协议动态显示/隐藏功能界面
 * - 新增：同步时间按钮（无弹窗，仅 log）
 */

// ==================== 全局变量 ====================
let bleDevice, gattServer;
let epdService, epdCharacteristic, txCharacteristic, cmdCharacteristic;
let startTime, msgIndex, appVersion;
let canvas, ctx, textDecoder;
let paintManager, cropManager;

// APP版本号
const APP_VERSION = '2.1.0';
const APP_BUILD_DATE = '2026-03-31';

let ditherBrightness = 1.0;    // 亮度系数

// 蓝牙命令定义（与固件保持一致）
const EpdCmd = {
    SET_PINS: 0x00,
    INIT: 0x01,
    CLEAR: 0x02,
    SEND_CMD: 0x03,
    SEND_DATA: 0x04,
    REFRESH: 0x05,
    SLEEP: 0x06,
    SET_TIME: 0x20,
    SET_WEEK_START: 0x21,
    WRITE_IMG: 0x30,           // v1.6 普通传输
    WRITE_BLOCK: 0x31,         // CRC传输块
    QUERY_STATUS: 0x32,        // 查询传输状态
    RESET_TRANSFER: 0x33,      // 重置传输状态
    
    SET_SLOT: 0x31,      // 设置/选择/显示槽位
    FREE_SLOT: 0x32,     // 释放槽位
    SET_SLIDE: 0x33,     // 轮播间隔
    GET_IMAGE: 0x34,     // 读取槽位图片
    GET_SLOTS: 0x35,     // 查询槽位信息
    
    SET_CONFIG: 0x90,
    SYS_RESET: 0x91,
    SYS_SLEEP: 0x92,
    CFG_ERASE: 0x99,
    SET_HOLIDAYS: 0xB6,        // 设置假期数据
    GHOSTING_CLEAR: 0xB7,      // 开始残影消除
    GHOSTING_STOP: 0xB8        // 停止残影消除
};

// 画布尺寸预设
const canvasSizes = [
    { name: '1.54_152_152', width: 152, height: 152 },
    { name: '1.54_200_200', width: 200, height: 200 },
    { name: '2.13_104_212', width: 104, height: 212 },
    { name: '2.13_212_104', width: 212, height: 104 },
    { name: '2.13_250_122', width: 250, height: 122 },
    { name: '2.13_128_250', width: 128, height: 250 },
    { name: '2.66_152_296', width: 152, height: 296 },//52810单独的
    { name: '2.66_296_152', width: 296, height: 152 },
    { name: '2.7_176_264', width: 176, height: 264 },//LG2.7寸黑白
    { name: '2.8_152_296', width: 152, height: 296 },//四色2.8寸
    { name: '2.9_296_128', width: 296, height: 128 },
    { name: '2.9_128_296', width: 128, height: 296 },//盒马2.9寸
    { name: '2.9_384_168', width: 384, height: 168 },
    { name: '3.1_300_300', width: 304, height: 304 },
    { name: '3.5_384_184', width: 384, height: 184 },
    { name: '3.68_792_528', width: 792, height: 528 },//3.68寸E6
    { name: '3.7_240_416', width: 240, height: 416 },//3.7寸 第一代AI智屏壳
    { name: '3.7_416_240', width: 416, height: 240 },
    { name: '3.97_800_480', width: 800, height: 480 },
    { name: '3.98_768_552', width: 768, height: 552 },//3.98寸四色手机壳
    { name: '4.2_400_300', width: 400, height: 300 },
    { name: '4.37_512_368', width: 512, height: 368 },//4.37四色
    { name: '5.79_792_272', width: 792, height: 272 },
    { name: '5.81_720_256', width: 720, height: 256 },//海带屏
    { name: '5.83_600_448', width: 600, height: 448 },
    { name: '5.83_648_480', width: 648, height: 480 },
    { name: '7.4_800_480', width: 800, height: 480 },//SES7.4_GU140
    { name: '7.5_640_384', width: 640, height: 384 },
    { name: '7.5_800_480', width: 800, height: 480 },
    { name: '7.5_880_528', width: 880, height: 528 },
    { name: '9.7_960_672', width: 960, height: 672 },//9.7寸Tsl
    { name: '9.7_960_680', width: 960, height: 680 },//9.7寸四色
    { name: '10.2_960_640', width: 960, height: 640 },
    { name: '10.85_1360_480', width: 1360, height: 480 },
    { name: '11.6_960_640', width: 960, height: 640 },
    { name: '4E_600_400', width: 600, height: 400 },
    { name: '7.3E6', width: 480, height: 800 }, 
    { name: '7.3E6_800_480', width: 800, height: 480 }
];

// ==================== 双协议支持 ====================
// 在现有全局变量下方添加
let appMtuNegotiated = false;

let appModeEnabled = false;
let currentEpdIndex = 1;
let compressEnabled = false;
let epdTypeForApp = 0x06;
let imageDataA = null, imageDataB = null, currentImageDataForApp = null;
// APP 模式专用：存储从主画布同步过来的图像数据
let storedImageDataA = null;   // ImageData 对象
let storedImageDataB = null;

// ==================== 图片槽位相关全局变量 ====================
let slotState = { count: 0, usedMask: 0n, selected: null, fingerprints: [] , totalSize: null   /* 新增：Flash 总容量（字节），null 表示旧固件未报告*/};
let slotReadState = null;              // 正在读取的槽位信息
let slotImageCache = new Map();        // 内存缓存：slot -> {width, height, size, colorId, dataUrl, previewKind, fingerprint}
let slotImageCacheScope = '';          // 用于区分不同设备/驱动的缓存作用域
let slotPreviewPending = new Set();    // 正在写入但未完成的槽位集合
let rleSupport = false;                // 设备是否支持 RLE 压缩传输
let imageTransferActive = false;       // 是否正在传输图片（用于锁定UI）
let imageRefreshPending = false;       // 🆕 屏幕刷新等待中
let imageRefreshTimer = null;          // 🆕 刷新超时定时器
let slotActionPending = false;         // 槽位操作（显示/删除等）进行中
let slotActionTimer = null;            // 🆕 槽位操作超时定时器
let slotReadTimer = null;
let slotEraseAllPending = false;

const MAX_SLOT_IMAGE_SIZE = 1024 * 1024;
const DEFAULT_SLOT_READ_RAW_CHUNK_SIZE = 256;
const SLOT_READ_TIMEOUT_MS = 5000;
const SLOT_READ_INFO_TIMEOUT_MS = 8000;
const SLOT_CHUNK_MAX_RETRIES = 2;
const IMAGE_REFRESH_TIMEOUT_MS = 95000;
const SLOT_IMAGE_CACHE_PREFIX = 'epd-slot-preview-v1:';
const SLOT_PREVIEW_MAX_EDGE = 480;         // 🆕 预览缩略图最大边长
const SLOT_PREVIEW_JPEG_QUALITY = 0.88;    // 🆕 JPEG 压缩质量

// ==================== 工具函数 ====================
function hex2bytes(hex) {
    const bytes = [];
    for (let i = 0; i < hex.length; i += 2) {
        bytes.push(parseInt(hex.substr(i, 2), 16));
    }
    return new Uint8Array(bytes);
}

function bytes2hex(data) {
    return new Uint8Array(data).reduce((memo, i) => memo + ("0" + i.toString(16)).slice(-2), "");
}

function intToHex(intIn) {
    let stringOut = ("0000" + intIn.toString(16)).substr(-4);
    return stringOut.substring(2, 4) + stringOut.substring(0, 2);
}

function resetVariables() {
    gattServer = null;
    epdService = null;
    epdCharacteristic = null;
    txCharacteristic = null;
    cmdCharacteristic = null;
    driverAuthorDetected = false;
    msgIndex = 0;
    const logEl = document.getElementById("log");
    if (logEl) logEl.innerHTML = '';
    bleWriteChain = Promise.resolve();
    currentPinsValue = '';
    slotState = {
        count: 0,
        usedMask: 0n,
        selected: null,
        fingerprints: []
    };
    if (slotReadTimer != null) clearTimeout(slotReadTimer);
    slotReadTimer = null;
    slotReadState = null;
    slotImageCache = new Map();
    slotImageCacheScope = '';
    slotPreviewPending = new Set();
    rleSupport = false;
    imageTransferActive = false;
    imageRefreshPending = false;
    if (imageRefreshTimer != null) clearTimeout(imageRefreshTimer);
    imageRefreshTimer = null;
    slotActionPending = false;
    slotEraseAllPending = false;
    displayErrorActive = false;
    if (slotActionTimer != null) clearTimeout(slotActionTimer);
    slotActionTimer = null;
    renderSlotGrid();
}

// ==================== RLE 压缩/解压 ====================
function rleEncode(data, maxLiteral = 128) {
    const input = data instanceof Uint8Array ? data : new Uint8Array(data);
    const output = [];
    let offset = 0;
    while (offset < input.length) {
        let runLength = 1;
        while (offset + runLength < input.length && runLength < 130 && input[offset + runLength] === input[offset]) {
            runLength++;
        }
        if (runLength >= 3) {
            output.push(0x80 | (runLength - 3), input[offset]);
            offset += runLength;
            continue;
        }
        const literalStart = offset;
        let literalLength = 0;
        while (offset < input.length && literalLength < maxLiteral &&
            !(offset + 2 < input.length && input[offset] === input[offset + 1] && input[offset] === input[offset + 2])) {
            offset++;
            literalLength++;
        }
        if (literalLength === 0) {
            literalLength = 1;
            offset++;
        }
        output.push(literalLength - 1);
        for (let index = literalStart; index < literalStart + literalLength; index++) output.push(input[index]);
    }
    return new Uint8Array(output);
}

function rleDecode(data) {
    const input = data instanceof Uint8Array ? data : new Uint8Array(data);
    const output = [];
    let offset = 0;
    while (offset < input.length) {
        const token = input[offset++];
        if ((token & 0x80) !== 0) {
            if (offset >= input.length) throw new Error('RLE repeat token is incomplete');
            const count = (token & 0x7F) + 3;
            const value = input[offset++];
            for (let index = 0; index < count; index++) output.push(value);
        } else {
            const count = token + 1;
            if (offset + count > input.length) throw new Error('RLE literal token is incomplete');
            for (let index = 0; index < count; index++) output.push(input[offset++]);
        }
    }
    return new Uint8Array(output);
}

// ==================== 槽位缓存管理 ====================
// 判断蓝牙是否连接
function isBleConnected() {
    return gattServer != null && gattServer.connected && epdCharacteristic != null;
}

function getSlotImageCacheScope() {
    const deviceId = bleDevice && (bleDevice.id || bleDevice.name) ? (bleDevice.id || bleDevice.name) : 'unknown-device';
    const driver = document.getElementById('epddriver');
    return `${deviceId}:${driver ? driver.value : 'unknown-driver'}`;
}

function getSlotImageCacheKey(slot) {
    return `${SLOT_IMAGE_CACHE_PREFIX}${encodeURIComponent(getSlotImageCacheScope())}:${slot}`;
}

function loadSlotImageCache() {
    const scope = getSlotImageCacheScope();
    if (scope !== slotImageCacheScope) {
        slotImageCache = new Map();
        slotImageCacheScope = scope;
    }

    for (let slot = 0; slot < slotState.count; slot++) {
        const used = (slotState.usedMask & (1n << BigInt(slot))) !== 0n;
        const pending = slotPreviewPending.has(slot);
        const fingerprint = slotState.fingerprints[slot] || null;

        // 如果槽位未使用且不在等待中 → 清理缓存
        if (!used && !pending) {
            removeSlotImageCache(slot);
            continue;
        }

        // 检查内存缓存是否与指纹匹配
        const currentEntry = slotImageCache.get(slot);
        if (used && !pending && currentEntry && !slotCacheMatchesFingerprint(currentEntry, fingerprint)) {
            slotImageCache.delete(slot);
            try { localStorage.removeItem(getSlotImageCacheKey(slot)); } catch (_) {}
            addLog(`🔄 槽位 ${slot + 1} 指纹已变更，旧缓存已清除。`);
        }

        // 从 localStorage 加载
        try {
            const stored = localStorage.getItem(getSlotImageCacheKey(slot));
            if (stored) {
                const entry = JSON.parse(stored);
                if (entry && entry.dataUrl && entry.dataUrl.startsWith('data:image/')) {
                    // 再次校验指纹
                    if (used && !pending && !slotCacheMatchesFingerprint(entry, fingerprint)) {
                        localStorage.removeItem(getSlotImageCacheKey(slot));
                        continue;
                    }
                    const cachedEntry = slotImageCache.get(slot);
                    const currentSavedAt = cachedEntry && Number(cachedEntry.savedAt) || 0;
                    const storedSavedAt = Number(entry.savedAt) || 0;
                    if (!cachedEntry || storedSavedAt > currentSavedAt) {
                        slotImageCache.set(slot, entry);
                    }
                }
            }
        } catch (error) {
            console.warn('Failed to load slot image cache', error);
            try { localStorage.removeItem(getSlotImageCacheKey(slot)); } catch (_) {}
        }

        // 如果槽位已使用且之前有 pending 标记，清除 pending
        if (used && pending) {
            slotPreviewPending.delete(slot);
            const entry = slotImageCache.get(slot);
            if (entry && entry.pending) {
                saveSlotImageCache(slot, { ...entry, fingerprint, pending: false });
            }
        }
    }
}

function saveSlotImageCache(slot, entry) {
    slotImageCache.set(slot, entry);
    const cacheKey = getSlotImageCacheKey(slot);
    const serializedEntry = JSON.stringify(entry);
    try {
        localStorage.setItem(cacheKey, serializedEntry);
        return true;
    } catch (firstError) {
        try {
            localStorage.removeItem(cacheKey);
            localStorage.setItem(cacheKey, serializedEntry);
            return true;
        } catch (error) {
            console.warn('Failed to persist slot image cache', firstError, error);
            addLog('浏览器缓存空间不足，本次预览仅在当前页面有效。');
            return false;
        }
    }
}

function removeSlotImageCache(slot) {
    slotPreviewPending.delete(slot);
    slotImageCache.delete(slot);
    try { localStorage.removeItem(getSlotImageCacheKey(slot)); } catch (_) { }
}

function clearAllSlotImageCaches() {
    for (let slot = 0; slot < Math.max(slotState.count, 20); slot++) removeSlotImageCache(slot);
    slotImageCache.clear();
}

function formatSlotBytes(size) {
    if (size < 1024) return `${size} B`;
    if (size < 1024 * 1024) return `${(size / 1024).toFixed(1)} KB`;
    return `${(size / 1024 / 1024).toFixed(1)} MB`;
}

function slotColorName(colorId) {
    return colorId === 2 ? '黑白' : colorId === 3 ? '黑白红' : colorId === 4 ? '黑白红黄' : colorId === 6 ? '黑白红黄蓝绿' :'黑白红黄绿蓝橙';
}

// ==================== 槽位辅助函数（指纹 / 预览） ====================

function normalizeSlotFingerprint(value) {
    return typeof value === 'string' && /^[0-9a-f]{8}$/i.test(value) ? value.toUpperCase() : null;
}

function slotCacheMatchesFingerprint(entry, fingerprint) {
    return fingerprint == null || normalizeSlotFingerprint(entry && entry.fingerprint) === fingerprint;
}

function createSlotPreviewDataUrl(sourceImageData) {
    const source = document.createElement('canvas');
    source.width = sourceImageData.width;
    source.height = sourceImageData.height;
    source.getContext('2d').putImageData(sourceImageData, 0, 0);

    const scale = Math.min(1, SLOT_PREVIEW_MAX_EDGE / Math.max(source.width, source.height));
    const preview = document.createElement('canvas');
    preview.width = Math.max(1, Math.round(source.width * scale));
    preview.height = Math.max(1, Math.round(source.height * scale));
    const previewCtx = preview.getContext('2d');
    previewCtx.fillStyle = '#fff';
    previewCtx.fillRect(0, 0, preview.width, preview.height);
    previewCtx.drawImage(source, 0, 0, preview.width, preview.height);

    const dataUrl = preview.toDataURL('image/jpeg', SLOT_PREVIEW_JPEG_QUALITY);
    if (!dataUrl.startsWith('data:image/')) throw new Error('Canvas preview snapshot failed');
    return dataUrl;
}

// ==================== 槽位数据旋转恢复（针对3.7寸特殊屏）====================
function get1bppPixel(data, width, x, y) {
    const pixelIndex = y * width + x;
    const byteIndex = pixelIndex >> 3;
    const shift = 7 - (pixelIndex & 0x07);
    return (data[byteIndex] >> shift) & 0x01;
}
function set1bppPixel(data, width, x, y, value) {
    const pixelIndex = y * width + x;
    const byteIndex = pixelIndex >> 3;
    const mask = 0x80 >> (pixelIndex & 0x07);
    if (value) data[byteIndex] |= mask;
    else data[byteIndex] &= ~mask;
}
function get2bppPixel(data, width, x, y) {
    const pixelIndex = y * width + x;
    const byteIndex = pixelIndex >> 2;
    const shift = 6 - ((pixelIndex & 0x03) * 2);
    return (data[byteIndex] >> shift) & 0x03;
}
function set2bppPixel(data, width, x, y, value) {
    const pixelIndex = y * width + x;
    const byteIndex = pixelIndex >> 2;
    const shift = 6 - ((pixelIndex & 0x03) * 2);
    data[byteIndex] = (data[byteIndex] & ~(0x03 << shift)) | ((value & 0x03) << shift);
}

function restoreRotated1bpp(data, width, height) {
    const output = new Uint8Array(Math.ceil(width * height / 8)).fill(0xFF);
    for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
            set1bppPixel(output, width, x, y, get1bppPixel(data, height, y, width - 1 - x));
        }
    }
    return output;
}

function restoreRotated2bpp(data, width, height) {
    const output = new Uint8Array(Math.ceil(width * height / 4));
    for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
            set2bppPixel(output, width, x, y, get2bppPixel(data, height, y, width - 1 - x));
        }
    }
    return output;
}

function normalizeSlotImageData(meta) {
    const driverSelect = document.getElementById('epddriver');
    const isGDEM037F51 = (driverSelect.value === '0d');
    const isGDEY037Z03 = (driverSelect.value === '0e' || driverSelect.value === '0f' || driverSelect.value === '12');
    const needsNativeRotation = meta.width === 416 && meta.height === 240 && (isGDEM037F51 || isGDEY037Z03);
    if (!needsNativeRotation) return meta.data;

    if (meta.colorId === 2) return restoreRotated2bpp(meta.data, meta.width, meta.height);
    if (meta.colorId === 0) return restoreRotated1bpp(meta.data, meta.width, meta.height);
    if (meta.colorId === 1) {
        const planeSize = Math.floor(meta.data.length / 2);
        const output = new Uint8Array(meta.data.length);
        output.set(restoreRotated1bpp(meta.data.slice(0, planeSize), meta.width, meta.height), 0);
        output.set(restoreRotated1bpp(meta.data.slice(planeSize), meta.width, meta.height), planeSize);
        return output;
    }
    return meta.data;
}

function decodeUC8159SlotData(data, width, height) {
    const imageData = new ImageData(width, height);
    for (let pixel = 0; pixel < width * height; pixel++) {
        const packed = data[pixel >> 1];
        const value = (pixel & 1) === 0 ? (packed >> 4) & 0x0F : packed & 0x0F;
        const index = pixel * 4;
        if (value === 0x04) {
            imageData.data[index] = 255;
            imageData.data[index + 1] = 0;
            imageData.data[index + 2] = 0;
        } else {
            const channel = value === 0x00 ? 0 : 255;
            imageData.data[index] = channel;
            imageData.data[index + 1] = channel;
            imageData.data[index + 2] = channel;
        }
        imageData.data[index + 3] = 255;
    }
    return imageData;
}

// 缓存当前画布内容作为槽位预览（存入槽位时调用）
function cacheCurrentSlotPreview(slot, processedData, mode) {
    try {
        const scope = getSlotImageCacheScope();
        if (scope !== slotImageCacheScope) {
            slotImageCache = new Map();
            slotImageCacheScope = scope;
        }
        const sourceImageData = ditherSourceImageData &&
            ditherSourceImageData.width === canvas.width && ditherSourceImageData.height === canvas.height ?
            ditherSourceImageData :
            ctx.getImageData(0, 0, canvas.width, canvas.height);
        const dataUrl = createSlotPreviewDataUrl(sourceImageData);
        const colorId = mode === 'blackWhiteColor' ? 2 : mode === 'threeColor' ? 3 : mode === 'fourColor' ? 4 : mode === 'sixColor' ? 6 : 7;
        slotPreviewPending.add(slot);
        saveSlotImageCache(slot, {
            width: canvas.width,
            height: canvas.height,
            size: processedData.length,
            colorId,
            dataUrl,
            previewKind: 'original',
            fingerprint: null,
            pending: true,
            savedAt: new Date().getTime()
        });
        renderSlotGrid(true);
        addLog(`槽位 ${slot + 1} 原图预览已生成，无需再次回读。`);
    } catch (error) {
        console.warn('Failed to cache current slot preview', error);
        removeSlotImageCache(slot);
        addLog(`槽位 ${slot + 1} 预览生成失败：${error.message || error}`);
    }
}

// ==================== 屏幕刷新超时管理 ====================

function cancelImageRefreshWait() {
    if (imageRefreshTimer != null) {
        clearTimeout(imageRefreshTimer);
        imageRefreshTimer = null;
    }
    imageRefreshPending = false;
}

function startImageRefreshWait() {
    cancelImageRefreshWait();
    imageRefreshPending = true;
    imageRefreshTimer = setTimeout(() => {
        if (!imageRefreshPending) return;
        imageRefreshPending = false;
        imageRefreshTimer = null;
        imageTransferActive = false;
        updateButtonStatus();
        setStatus('⚠️ 屏幕刷新完成通知超时，控制按钮已恢复。');
        addLog('⚠️ 屏幕刷新完成通知超时（95s），控制按钮已恢复；请确认屏幕已停止刷新后再操作。');
    }, IMAGE_REFRESH_TIMEOUT_MS);
}

function completeImageRefresh() {
    if (!imageRefreshPending) return false;

    cancelImageRefreshWait();
    imageTransferActive = false;
    updateButtonStatus();
    const totalTime = (Date.now() - startTime) / 1000.0;
    setStatus(`✅ 屏幕刷新完成！总耗时: ${totalTime.toFixed(1)}s`);
    addLog(`✅ 屏幕刷新完成，可以继续操作。总耗时: ${totalTime.toFixed(1)}s`);
    const statusEl = document.getElementById('status');
    if (statusEl) {
        setTimeout(() => {
            statusEl.parentElement.style.display = 'none';
        }, 5000);
    }
    return true;
}

// ==================== 蓝牙写入（带防冲突锁）====================
let writeInProgress = false;
const WRITE_DELAY_MS = 20;
function sleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }

async function write(cmd, data, withResponse = true) {
    while (writeInProgress) await sleep(10);
    if (!epdCharacteristic) {
        addLog("服务不可用，请检查蓝牙连接");
        return false;
    }
    writeInProgress = true;
    try {
        let body = new Uint8Array(0);
        if (data) {
            if (typeof data === 'string') data = hex2bytes(data);
            if (data instanceof Uint8Array) body = data;else body = Uint8Array.from(data);
        }
        const dataBuffer = new Uint8Array(body.length + 1);
        dataBuffer[0] = cmd;
        dataBuffer.set(body, 1);
        if (cmd !== EpdCmd.WRITE_IMG || withResponse) addLog(bytes2hex(dataBuffer), '⇑');
        
        // ==============================================
        // 🔥 核心兼容写法：自动适配所有浏览器/设备
        // ==============================================
        if (withResponse) {
            // 带响应写入（兼容新老API）
            if (epdCharacteristic.writeValueWithResponse) {
                await epdCharacteristic.writeValueWithResponse(dataBuffer);
            } else {
                await epdCharacteristic.writeValue(dataBuffer);
            }
        } else {
            // 不带响应写入（兼容新老API）
            if (epdCharacteristic.writeValueWithoutResponse) {
                await epdCharacteristic.writeValueWithoutResponse(dataBuffer);
            } else {
                await epdCharacteristic.writeValue(dataBuffer);
            }
        }
        if (withResponse && WRITE_DELAY_MS > 0) await sleep(WRITE_DELAY_MS);
        return true;
    } catch (e) {
        console.error(e);
        if (e.message) addLog("write: " + e.message);
        return false;
    } finally {
        writeInProgress = false;
    }
}

// ==================== 图像传输（支持CRC模式）====================
async function writeImage(data, step = 'bw') {
    const configuredMtu = parseInt(document.getElementById('mtusize').value, 10);
    const configuredInterval = parseInt(document.getElementById('interleavedcount').value, 10);
    const mtu = Math.max(1, (Number.isFinite(configuredMtu) ? configuredMtu : 20) - 2);
    const interleavedCount = Number.isFinite(configuredInterval) && configuredInterval >= 0
        ? configuredInterval
        : 20;
    const count = Math.ceil(data.length / mtu);
    let chunkIdx = 0;
    let noReplyCount = interleavedCount;
    for (let i = 0; i < data.length; i += mtu) {
        if (chunkIdx % 10 === 0 || chunkIdx + 1 === count) {
            const currentTime = (Date.now() - startTime) / 1000.0;
            setStatus(`${step === 'bw' ? '黑白' : '颜色'}块: ${chunkIdx + 1}/${count}, 总用时: ${currentTime}s`);
        }
        const chunk = data.subarray(i, Math.min(i + mtu, data.length));
        const payload = new Uint8Array(chunk.length + 1);
        //payload[0] = (step === 'bw' ? 0x0F : 0x00) | (i === 0 ? 0x00 : 0xF0);
        payload[0] = (step === 'blue' && i === 0) ? 0x01 : (step === 'bw' ? 0x0F : 0x00) | (i === 0 ? 0x00 : 0xF0);
        payload.set(chunk, 1);
        if (noReplyCount > 0) {
            await write(EpdCmd.WRITE_IMG, payload, false);
            noReplyCount--;
        } else {
            await write(EpdCmd.WRITE_IMG, payload, true);
            noReplyCount = interleavedCount;
        }
        chunkIdx++;
    }
}

var a0_fix = 0;
let driverAuthorDetected = false;    // 是否已识别驱动作者
let deviceDriverValue = null;    // 存储设备上报的驱动值（如 "06"）
// 使用CRC校验传输（如果固件支持）
async function writeImageCRC(data, step = 'bw') {
    const stepName = step === 'bw' ? '黑白' : '颜色';
    try {
        const epdDriverSelect = document.getElementById('epddriver');
        const epdDriverPreset = document.getElementById('driverPreset');
        addLog(`驱动预设: ${epdDriverPreset.value}  驱动ID:${epdDriverSelect.value}`);
        if(epdDriverPreset.value == "tsl0922" && epdDriverSelect.value == "13" && a0_fix != 1) data = JD79660JiaoCuoYuChuLi(data);
        await BleTransfer.sendImageWithResume(data, step, (sent, total, speedInfo) => {
            if (speedInfo) {
                setStatus(`${stepName}块(CRC): ${sent}/${total}, ${BleTransfer.getSpeedString()}, ${speedInfo.elapsed}s`);
            } else {
                setStatus(`${stepName}块(CRC): ${sent}/${total}`);
            }
        });
        return true;
    } catch (e) {
        console.error('CRC transfer failed:', e);
        addLog(`CRC传输失败: ${e.message}，回退到普通传输`);
        await writeImage(data, step);
        return true;
    }
}

// ==================== 设备控制 ====================
async function setDriver() {
    if (!confirm('确认设置驱动配置？此操作将重新初始化屏幕。')) return;
    await write(EpdCmd.SET_PINS, document.getElementById("epdpins").value);
    await write(EpdCmd.INIT, document.getElementById("epddriver").value);
    addLog("驱动配置已设置");
    a0_fix = 0;   // 重置交错处理标志，因为驱动已切换
    if(document.getElementById('driverPreset').value == "tsl0922") addLog("驱动配置已设置，a0_fix 已重置为 0");
}

function getWeekStart() {
    const weekStartValue = document.getElementById('weekStart').value;
    return weekStartValue !== null && weekStartValue !== '' ? parseInt(weekStartValue) : 1;
}

function buildTimeData(mode) {
    const timestamp = new Date().getTime() / 1000;
    return new Uint8Array([
        (timestamp >> 24) & 0xFF,
        (timestamp >> 16) & 0xFF,
        (timestamp >> 8) & 0xFF,
        timestamp & 0xFF,
        -(new Date().getTimezoneOffset() / 60),
        mode
    ]);
}

async function sendTimeCommand(mode, modeName) {
    const weekStart = getWeekStart();
    const weekDays = ['周日', '周一', '周二', '周三', '周四', '周五', '周六'];
    await write(EpdCmd.SET_WEEK_START, new Uint8Array([weekStart]));
    if (await write(EpdCmd.SET_TIME, buildTimeData(mode))) {
        addLog(`${modeName}已启用！`);
        addLog(`星期第一天已设置为：${weekDays[weekStart]}`);
        addLog("屏幕刷新完成前请不要操作。");
        return true;
    }
    return false;
}

// 老款时钟模式 (仅适用于UC8179 7.5寸)
async function syncTimeLegacy() {
    if (!confirm('确认切换到老款时钟模式？\n\n⚠️ 警告：时钟模式会加速屏幕老化导致损坏！\n• 请勿长时间使用\n• 此模式仅适用于UC8179 7.5寸屏幕\n• 费电')) return;
    await sendTimeCommand(3, '老款时钟模式');
}

async function syncTime(mode) {
    if (mode === 2 && !confirm("提醒：时钟模式目前使用全刷实现，此功能目前多用于修复老化屏残影问题，不建议长期开启，是否继续？")) return;
    if (mode === 1) {
        await syncHolidayData();
        await sleep(200);
    }
    const timestamp = Math.floor(Date.now() / 1000);
    const data = new Uint8Array([
        (timestamp >> 24) & 0xFF,
        (timestamp >> 16) & 0xFF,
        (timestamp >> 8) & 0xFF,
        timestamp & 0xFF,
        -(new Date().getTimezoneOffset() / 60),
        mode
    ]);

    // 发送星期第一天设置
    const weekStart = getWeekStart();
    const weekDays = ['周日', '周一', '周二', '周三', '周四', '周五', '周六'];
    await write(EpdCmd.SET_WEEK_START, new Uint8Array([weekStart]));

    // 发送时间（仅一次）
    if (await write(EpdCmd.SET_TIME, data)) {
        addLog(`时间已同步！模式：${mode === 1 ? '日历模式' : '时钟模式'}`);
        addLog(`星期第一天已设置为：${weekDays[weekStart]}`);
        addLog("屏幕刷新完成前请不要操作。");
    }
}
// ==================== 新增：无弹窗同步时间 ====================
async function syncTimeOnly() {
    // 仅对 Web 模式有效，APP 模式下该按钮应被隐藏
    const timestamp = Math.floor(Date.now() / 1000);
    const data = new Uint8Array([
        (timestamp >> 24) & 0xFF,
        (timestamp >> 16) & 0xFF,
        (timestamp >> 8) & 0xFF,
        timestamp & 0xFF,
        -(new Date().getTimezoneOffset() / 60),
        1   // 日历模式（仅为时间同步，模式值随意）
    ]);
    const success = await write(EpdCmd.SET_TIME, data);
    if (success) {
        addLog(`✅ 已同步时间: ${new Date(timestamp * 1000).toLocaleString()}`);
    } else {
        addLog("❌ 时间同步失败");
    }
}

async function clearScreen() {
    if (confirm('确认清除屏幕内容?')) {
        await write(EpdCmd.CLEAR);
        addLog("清屏指令已发送！");
        addLog("屏幕刷新完成前请不要操作。");
    }
}

async function sendcmd() {
    const cmdTXT = document.getElementById('cmdTXT').value;
    if (!cmdTXT) return;
    const bytes = hex2bytes(cmdTXT);
    await write(bytes[0], bytes.length > 1 ? bytes.slice(1) : null);
    addLog("命令已发送");
}

// ==================== 槽位核心功能 ====================
function setSlotActionPending(pending) {
    slotActionPending = pending;
    // 清除旧定时器
    if (slotActionTimer != null) {
        clearTimeout(slotActionTimer);
        slotActionTimer = null;
    }
    if (pending) {
        // 95 秒超时自动解锁，防止永久卡死
        slotActionTimer = setTimeout(() => {
            slotActionPending = false;
            slotEraseAllPending = false;
            slotActionTimer = null;
            updateButtonStatus();
            addLog('槽位操作等待超时（95s），控制按钮已自动恢复。');
        }, 95000);
    }
    updateButtonStatus();
}

function applySlotsMessage(message) {
    // 格式: slots=count usedMask [selected] [fingerprint1] [fingerprint2] ...
    // 例如: slots=5 0x1F 0 ABCD1234 5678EFGH ...
    const parts = message.trim().split(/\s+/);
    const countMatch = /^slots=(\d+)$/.exec(parts[0] || '');
    if (!countMatch || parts.length < 2 || !/^(?:0x[0-9a-f]+|\d+)$/i.test(parts[1])) {
        return false;
    }

    const count = parseInt(countMatch[1], 10);
    let totalSize = null;
    let fingerprintStart = 2;   // 默认从 parts[2] 开始尝试读取 selected
    let selected = null;
    // 如果第三个字段是纯数字（0~255），则它是 selected 索引
    if (parts[2] != null && /^\d+$/.test(parts[2])) {
        selected = parseInt(parts[2], 10);
        fingerprintStart = 3;
    }
    
    // 2. 检查是否包含 size= 字段（新固件）
    if (parts.length > fingerprintStart && parts[fingerprintStart].startsWith('size=')) {
        const sizeStr = parts[fingerprintStart].substring(5);
        totalSize = parseInt(sizeStr, 10);
        fingerprintStart++;   // size 字段占用一个位置，指纹往后移
    }
    
    
    // 提取指纹（每个指纹应为 8 位十六进制）
    //const fingerprints = parts.slice(fingerprintStart, fingerprintStart + count)
        //.map(s => /^[0-9a-f]{8}$/i.test(s) ? s.toUpperCase() : null);
    // 3. 提取指纹（从 fingerprintStart 开始，取 count 个）
    const fingerprints = [];
    for (let i = 0; i < count; i++) {
        const idx = fingerprintStart + i;
        if (idx < parts.length && /^[0-9a-f]{8}$/i.test(parts[idx])) {
            fingerprints.push(parts[idx].toUpperCase());
        } else {
            fingerprints.push(null);
        }
    }

    // 4. 更新全局状态
    slotState = {
        count,
        usedMask: BigInt(parts[1]), 
        selected,
        fingerprints, 
        totalSize: isNaN(totalSize) ? null : totalSize
    };

    // 加载缓存（会自动校验指纹）
    loadSlotImageCache();

    // 处理擦除全部完成
    const eraseAllCompleted = slotEraseAllPending && slotState.usedMask === 0n;
    if (slotEraseAllPending && !eraseAllCompleted) {
        updateButtonStatus();
        return true;
    }
    slotEraseAllPending = false;
    if (slotActionPending) setSlotActionPending(false);
    else updateButtonStatus();

    if (eraseAllCompleted) {
        clearAllSlotImageCaches();
        const status = document.getElementById('slotReadStatus');
        if (status) {
            status.hidden = false;
            status.textContent = '✅ 全部图片槽位已擦除。';
        }
        addLog('✅ 全部图片槽位擦除完成。');
    }
    renderSlotGrid();
    return true;
}

async function refreshSlots() {
    if (!isBleConnected()) return;
    addLog('正在读取图片槽位...');
    await write(EpdCmd.GET_SLOTS);
}

function renderSlotGrid(forceDisabled = imageTransferActive || slotActionPending || slotReadState !== null) {
    const grid = document.getElementById('slotGrid');
    const summary = document.getElementById('slotSummary');
    const hint = document.getElementById('slotHint');
    if (!grid || !summary || !hint) return;

    grid.replaceChildren();
    if (!isBleConnected()) {
        summary.textContent = '连接设备后读取槽位';
        hint.textContent = '图片保存在设备外置 Flash 中';
        return;
    }

    if (slotState.count === 0) {
        summary.textContent = '未识别到外置 Flash';
        hint.textContent = '请检查 Flash 供电及 P0.12 至 P0.15 连线';
        return;
    }

    let usedCount = 0;
    for (let slot = 0; slot < slotState.count; slot++) {
        const used = (slotState.usedMask & (1n << BigInt(slot))) !== 0n;
        const cached = slotImageCache.get(slot) || null;
        const previewPending = !used && cached && slotPreviewPending.has(slot);
        if (used) usedCount++;

        const item = document.createElement('div');
        item.className = used ? 'slot-item used' : 'slot-item';
        if (slotState.selected === slot) item.classList.add('selected');

        const label = document.createElement('div');
        label.className = 'slot-label';
        const title = document.createElement('strong');
        title.textContent = `槽位 ${slot + 1}`;
        const state = document.createElement('span');
        state.className = 'slot-state';
        state.textContent = `${used ? '已存图片' : previewPending ? '正在存入' : '空闲'}${cached ? ' · 已缓存' : used ? ' · 未读取' : ''}${slotState.selected === slot ? ' · 当前' : ''}`;
        label.append(title, state);

        const actions = document.createElement('div');
        actions.className = 'slot-actions';

        const saveButton = document.createElement('button');
        saveButton.type = 'button';
        saveButton.className = 'primary';
        saveButton.textContent = used ? '覆盖' : '存入';
        saveButton.disabled = forceDisabled;
        saveButton.addEventListener('click', () => saveImageToSlot(slot));

        const displayButton = document.createElement('button');
        displayButton.type = 'button';
        displayButton.className = 'secondary';
        displayButton.textContent = '显示';
        displayButton.disabled = forceDisabled || !used;
        displayButton.addEventListener('click', () => displayImageSlot(slot));

        const readControl = document.createElement('div');
        readControl.className = cached ? 'slot-read-control cached' : 'slot-read-control';
        const readButton = document.createElement('button');
        readButton.type = 'button';
        readButton.className = 'secondary';
        readButton.textContent = '读取';
        readButton.disabled = forceDisabled || !used;
        readButton.addEventListener('click', () => readImageSlot(slot));

        const hoverPreview = document.createElement('div');
        hoverPreview.className = cached ? 'slot-hover-preview cached' : 'slot-hover-preview empty';
        hoverPreview.id = `slotPreviewTooltip${slot}`;
        hoverPreview.setAttribute('role', 'tooltip');
        readButton.setAttribute('aria-describedby', hoverPreview.id);
        readButton.title = cached ? '悬停预览已缓存图片' : '点击读取图片并生成网页缓存';
        if (cached) {
            const previewImage = document.createElement('img');
            previewImage.src = cached.dataUrl;
            previewImage.alt = `槽位 ${slot + 1} 缓存预览`;
            const previewMeta = document.createElement('span');
            const previewKind = cached.previewKind === 'original' ? '原图' : '设备回读';
            previewMeta.textContent = `${cached.width} × ${cached.height} · ${slotColorName(cached.colorId)} · ${previewKind}`;
            hoverPreview.append(previewImage, previewMeta);
        } else {
            hoverPreview.textContent = used ? '尚未读取，点击“读取”后可悬停预览' : '空槽位，无图片可读取';
        }
        readControl.append(readButton, hoverPreview);

        const freeButton = document.createElement('button');
        freeButton.type = 'button';
        freeButton.className = 'secondary slot-delete';
        freeButton.textContent = '删除';
        freeButton.disabled = forceDisabled || !used;
        freeButton.addEventListener('click', () => freeImageSlot(slot));

        actions.append(saveButton, displayButton, readControl, freeButton);
        item.append(label, actions);
        grid.appendChild(item);
    }

    //summary.textContent = `${slotState.count} 个槽位，已使用 ${usedCount} 个`;
    let infoText = `${slotState.count} 个槽位，已使用 ${usedCount} 个`;
    if (slotState.totalSize) {
        const sizeKB = slotState.totalSize / 1024;
        if (sizeKB >= 1024) {
            const sizeMB = (sizeKB / 1024).toFixed(1);
            infoText += `，总容量 ${sizeMB} MB`;
        } else {
            infoText += `，总容量 ${sizeKB.toFixed(1)} KB`;
        }
    } else {
        infoText += `，容量未知（旧固件）`;
    }
    summary.textContent = infoText;
    hint.textContent = '“存入”会同时刷新屏幕并保存当前画布';
}

async function saveImageToSlot(slot) {
    if (imageTransferActive || slotActionPending) return;
    const imageFile = document.getElementById('imageFile');
    if (!imageFile || imageFile.files.length === 0) {
        alert('请先选择图片，再存入图片槽。');
        addLog(`槽位 ${slot + 1} 未存入：尚未选择图片。`);
        return;
    }
    const used = (slotState.usedMask & (1n << BigInt(slot))) !== 0n;
    if (used && !confirm(`槽位 ${slot + 1} 已有图片，确认覆盖？`)) return;
    // 传入 noRefresh: true
    await sendimg({ slot, noRefresh: true });
}

async function freeImageSlot(slot) {
    if (imageTransferActive || slotActionPending) return;
    if (!confirm(`确认删除槽位 ${slot + 1} 的图片？`)) return;
    setSlotActionPending(true);
    if (await write(EpdCmd.FREE_SLOT, new Uint8Array([slot]))) {
        removeSlotImageCache(slot);
        renderSlotGrid(true);
        addLog(`槽位 ${slot + 1} 删除命令已发送。`);
    } else {
        setSlotActionPending(false);
    }
}

async function freeAllImageSlots() {
    if (imageTransferActive || slotActionPending || slotReadState || slotState.usedMask === 0n) return;
    if (!confirm('确认擦除全部图片槽位？所有已保存图片都将永久删除，此操作不可恢复。')) return;

    slotEraseAllPending = true;
    setSlotActionPending(true);
    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = '正在擦除全部图片槽位，请勿断开连接...';
    if (await write(EpdCmd.FREE_SLOT, new Uint8Array([0xFF]))) {
        addLog('全部图片槽位擦除命令已发送。');
    } else {
        slotEraseAllPending = false;
        setSlotActionPending(false);
        status.textContent = '全部槽位擦除命令发送失败。';
    }
}

async function displayImageSlot(slot) {
    if (imageTransferActive || slotActionPending) return;
    setSlotActionPending(true);
    if (await write(EpdCmd.SET_SLOT, new Uint8Array([1, slot]))) {
        addLog(`已请求设备显示槽位 ${slot + 1}。`);
    } else {
        setSlotActionPending(false);
    }
}

async function stopSlotSlide() {
    if (await write(EpdCmd.SET_SLIDE, new Uint8Array([0, 0]))) {
        addLog('图片轮播已停止。');
    }
}

// ==================== 读取槽位图片（分块接收）====================
function clearSlotReadTimer() {
    if (slotReadTimer != null) clearTimeout(slotReadTimer);
    slotReadTimer = null;
}

function failSlotImageRead(message) {
    clearSlotReadTimer();
    slotReadState = null;
    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = message;
    addLog(message);
    updateButtonStatus();
}

function armSlotChunkTimeout(index) {
    clearSlotReadTimer();
    const state = slotReadState;
    slotReadTimer = setTimeout(() => {
        if (slotReadState === state) retrySlotChunk(index, '接收超时');
    }, SLOT_READ_TIMEOUT_MS);
}

function retrySlotChunk(index, reason) {
    const state = slotReadState;
    if (!state || state.pending || state.nextChunkIndex !== index) return;

    clearSlotReadTimer();
    state.expectedChunk = null;
    if (state.chunkRetries >= SLOT_CHUNK_MAX_RETRIES) {
        failSlotImageRead(`第 ${index + 1} 个数据块${reason}，重试 ${SLOT_CHUNK_MAX_RETRIES} 次后读取已停止。`);
        return;
    }

    state.chunkRetries++;
    addLog(`第 ${index + 1} 个数据块${reason}，正在重试 (${state.chunkRetries}/${SLOT_CHUNK_MAX_RETRIES})。`);
    void requestSlotChunk(index, true);
}

async function requestSlotChunk(index, retry = false) {
    const state = slotReadState;
    if (!state || state.pending) return;

    if (!retry) state.chunkRetries = 0;
    state.nextChunkIndex = index;
    state.expectedChunk = null;
    armSlotChunkTimeout(index);
    const request = new Uint8Array([state.slot, (index >> 8) & 0xFF, index & 0xFF]);
    if (!await write(EpdCmd.GET_IMAGE, request, false) && slotReadState === state && state.nextChunkIndex === index) {
        retrySlotChunk(index, '请求失败');
    }
}

function beginSlotImageRead(message) {
    const match = /^img=(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)(?:\s+(\d+))?$/.exec(message.trim());
    if (!match) return false;

    const slot = parseInt(match[1], 10);
    if (slotReadState && !slotReadState.pending && slotReadState.slot === slot) return true;

    const size = parseInt(match[4], 10);
    if (!Number.isFinite(size) || size <= 0 || size > MAX_SLOT_IMAGE_SIZE) {
        failSlotImageRead(`槽位图片大小异常：${size} 字节`);
        return true;
    }

    const startedAt = slotReadState && slotReadState.startedAt ?
        slotReadState.startedAt :
        new Date().getTime();
    clearSlotReadTimer();
    slotReadState = {
        slot,
        width: parseInt(match[2], 10),
        height: parseInt(match[3], 10),
        size,
        colorId: parseInt(match[5], 10),
        data: new Uint8Array(size),
        received: 0,
        expectedChunk: null,
        nextChunkIndex: 0,
        chunkRetries: 0,
        nextLogPercent: 10,
        rawChunkSize: match[6] == null ? DEFAULT_SLOT_READ_RAW_CHUNK_SIZE : parseInt(match[6], 10),
        startedAt,
        pending: false
    };

    if (!Number.isFinite(slotReadState.rawChunkSize) || slotReadState.rawChunkSize <= 0 ||
        slotReadState.rawChunkSize > 4096) {
        failSlotImageRead(`槽位数据块大小异常：${slotReadState.rawChunkSize}`);
        return true;
    }

    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = `槽位 ${slotReadState.slot + 1}：准备接收 ${formatSlotBytes(size)}`;
    void requestSlotChunk(0);
    return true;
}

function beginSlotChunk(message) {
    if (!slotReadState) return false;
    const match = /^chunk=(\d+)\s+len=(\d+)(?:\s+rle=(\d+))?$/.exec(message.trim());
    if (!match) return false;

    const index = parseInt(match[1], 10);
    if (index !== slotReadState.nextChunkIndex) {
        failSlotImageRead(`数据块序号异常：应为 ${slotReadState.nextChunkIndex + 1}，实际为 ${index + 1}。`);
        return true;
    }

    slotReadState.expectedChunk = {
        index,
        length: parseInt(match[2], 10),
        compressed: match[3] === '1',
        received: 0,
        parts: []
    };
    armSlotChunkTimeout(index);
    return true;
}

function receiveSlotChunk(data) {
    if (!slotReadState || !slotReadState.expectedChunk) return false;

    const expected = slotReadState.expectedChunk;
    if (expected.received + data.length > expected.length) {
        failSlotImageRead(`第 ${expected.index + 1} 个数据块长度异常，读取已停止。`);
        return true;
    }

    expected.parts.push(data.slice());
    expected.received += data.length;
    if (expected.received < expected.length) {
        armSlotChunkTimeout(expected.index);
        return true;
    }

    const chunkData = new Uint8Array(expected.length);
    let chunkOffset = 0;
    for (const part of expected.parts) {
        chunkData.set(part, chunkOffset);
        chunkOffset += part.length;
    }
    slotReadState.expectedChunk = null;

    let decoded;
    try {
        decoded = expected.compressed ? rleDecode(chunkData) : chunkData;
    } catch (error) {
        console.error(error);
        failSlotImageRead(`第 ${expected.index + 1} 个 RLE 数据块解析失败。`);
        return true;
    }

    const remaining = slotReadState.size - slotReadState.received;
    const expectedRawLength = Math.min(slotReadState.rawChunkSize, remaining);
    if (decoded.length !== expectedRawLength) {
        failSlotImageRead(`第 ${expected.index + 1} 个数据块解压长度异常。`);
        return true;
    }

    slotReadState.data.set(decoded, slotReadState.received);
    slotReadState.received += decoded.length;
    const percent = Math.round(slotReadState.received * 100 / slotReadState.size);
    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = `正在读取槽位 ${slotReadState.slot + 1}：${percent}% (${formatSlotBytes(slotReadState.received)} / ${formatSlotBytes(slotReadState.size)})`;

    if (percent >= slotReadState.nextLogPercent || slotReadState.received === slotReadState.size) {
        addLog(`槽位 ${slotReadState.slot + 1} 读取进度：${percent}%`, '⇓');
        while (slotReadState.nextLogPercent <= percent) slotReadState.nextLogPercent += 10;
    }

    if (slotReadState.received === slotReadState.size) {
        finishSlotImageRead();
    } else {
        void requestSlotChunk(expected.index + 1);
    }
    return true;
}

function finishSlotImageRead() {
    const meta = slotReadState;
    const elapsed = (new Date().getTime() - meta.startedAt) / 1000.0;
    clearSlotReadTimer();
    slotReadState = null;
    try {
        const mode = meta.colorId === 2 ? 'blackWhiteColor' : meta.colorId === 3 ? 'threeColor' : meta.colorId === 4 ? 'fourColor' : meta.colorId === 6 ? 'sixColor' : 'sevenColor';
        const normalized = normalizeSlotImageData(meta);
        const driverValue = document.getElementById('epddriver').value.toLowerCase();
        const imageData = (driverValue === '08' || driverValue === '09') ?
            decodeUC8159SlotData(normalized, meta.width, meta.height) :
            decodeProcessedData(normalized, meta.width, meta.height, mode);
        const existingPreview = slotImageCache.get(meta.slot);
        if (!existingPreview || existingPreview.previewKind !== 'original') {
            saveSlotImageCache(meta.slot, {
                width: meta.width,
                height: meta.height,
                size: meta.size,
                colorId: meta.colorId,
                dataUrl: createSlotPreviewDataUrl(imageData),
                previewKind: 'device',
                fingerprint: slotState.fingerprints[meta.slot] || null,
                savedAt: new Date().getTime()
            });
        }
        renderSlotGrid();

        const status = document.getElementById('slotReadStatus');
        status.hidden = false;
        status.textContent = `槽位 ${meta.slot + 1} 读取完成，悬停“读取”按钮即可预览。耗时 ${elapsed}s。`;
        addLog(`槽位 ${meta.slot + 1} 图片已缓存，耗时: ${elapsed}s。`);
    } catch (error) {
        console.error(error);
        const status = document.getElementById('slotReadStatus');
        status.hidden = false;
        status.textContent = '图片数据解析失败。';
    } finally {
        updateButtonStatus();
    }
}

async function readImageSlot(slot) {
    if (slotImageCache.has(slot)) {
        addLog(`槽位 ${slot + 1} 已有网页缓存，悬停“读取”按钮即可预览。`);
        return;
    }
    if (slotReadState) {
        addLog('已有槽位图片正在读取，请稍候。');
        return;
    }
    if (imageTransferActive || slotActionPending) return;

    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = `正在读取槽位 ${slot + 1}...`;
    slotReadState = {
        slot,
        pending: true,
        infoAttempts: 0,
        startedAt: new Date().getTime()
    };
    updateButtonStatus();
    await requestSlotImageInfo(slotReadState);
}

async function requestSlotImageInfo(state) {
    if (!state || slotReadState !== state || !state.pending) return;

    state.infoAttempts++;
    clearSlotReadTimer();
    slotReadTimer = setTimeout(() => {
        if (slotReadState !== state || !state.pending) return;
        if (state.infoAttempts < 2) {
            addLog('设备未返回图片信息，正在重试。');
            void requestSlotImageInfo(state);
        } else {
            failSlotImageRead('设备未返回图片信息，读取超时。');
        }
    }, SLOT_READ_INFO_TIMEOUT_MS);

    if (!await write(EpdCmd.GET_IMAGE, new Uint8Array([state.slot]), false) && slotReadState === state) {
        if (state.infoAttempts < 2) {
            addLog('读取命令发送失败，正在重试。');
            void requestSlotImageInfo(state);
        } else {
            failSlotImageRead('读取命令发送失败。');
        }
    }
}

// ==================== 错误处理 ====================

function handleDisplayError(code) {
    const busyTimeout = code === 'busy_timeout';
    const message = busyTimeout
        ? '⚠️ 屏幕 BUSY 等待超时，当前驱动可能与屏幕不匹配。请切换对应屏幕驱动后重试，蓝牙连接将保持。'
        : '⚠️ 设备正在执行其他显示操作，请稍后重试。';

    cancelImageRefreshWait();
    imageTransferActive = false;
    if (slotActionPending) setSlotActionPending(false);
    if (slotReadState) failSlotImageRead(message);
    const statusEl = document.getElementById('status');
    if (statusEl) {
        statusEl.parentElement.style.display = 'block';
        setStatus(message);
    }
    addLog(message, '', 'error');
    updateButtonStatus();
}

async function startSlotSlide(randomMode = false) {
    if (slotState.usedMask === 0n) {
        alert('请先存入至少一张图片，再启动轮播。');
        addLog('❌ 轮播未启动：没有可用的图片槽。');
        return false;
    }
    const input = document.getElementById('slotSlideMinutes');
    const minutes = Math.max(1, Math.min(65535, parseInt(input.value, 10) || 1));
    input.value = minutes;
    setSlotActionPending(true);
    const cmdData = new Uint8Array([minutes >> 8, minutes & 0xFF, randomMode ? 1 : 0]);
    if (await write(EpdCmd.SET_SLIDE, cmdData)) {
        addLog(`${randomMode ? '🎲 随机' : '🔄 顺序'}轮播已启动，间隔 ${minutes} 分钟。`);
        return true;
    }
    setSlotActionPending(false);
    return false;
}

// 🆕 随机轮播入口（HTML 已有按钮调用）
async function startRandomSlotSlide() {
    return startSlotSlide(true);
}

// ==================== 残影消除模式 ====================
async function startGhostingClearModeAsync(cycles) {
    const data = new Uint8Array([(cycles >> 8) & 0xFF, cycles & 0xFF]);
    await write(EpdCmd.GHOSTING_CLEAR, data, false);
    addLog(`残影消除模式已启动，将执行 ${cycles} 次清除流程`);
    addLog("指令已发送，准备自动断开连接...");
    setTimeout(() => {
        if (bleDevice && bleDevice.gatt && bleDevice.gatt.connected) {
            bleDevice.gatt.disconnect();
        }
    }, 300);
}

function startGhostingClearMode() {
    const cyclesInput = document.getElementById('ghostingCycles');
    let cycles = parseInt(cyclesInput.value);
    if (isNaN(cycles) || cycles < 1 || cycles > 1000) {
        alert("请输入有效的执行次数（1-1000）");
        return;
    }
    if (confirm(`确认要执行残影消除模式吗？\n将执行 ${cycles} 次清除流程\n每次流程约需30秒\n总计约需 ${Math.ceil(30 * cycles / 60)} 分钟`)) {
        setTimeout(() => {
            startGhostingClearModeAsync(cycles).catch(e => {
                console.error(e);
                addLog("残影消除指令发送失败");
            });
        }, 0);
    }
}

function stopGhostingClearMode() {
    if (confirm("确认要退出残影消除模式吗？")) {
        setTimeout(() => {
            write(EpdCmd.GHOSTING_STOP, null, false).then(success => {
                if (success) addLog("已发送退出残影消除指令");
            }).catch(e => {
                console.error(e);
                addLog("退出残影消除指令发送失败");
            });
        }, 0);
    }
}

// ==================== UC8159 特殊转换 ====================
function convertUC8159(blackWhiteData, redWhiteData) {
    const halfLength = blackWhiteData.length;
    const payloadData = new Uint8Array(halfLength * 4);
    let idx = 0;
    for (let i = 0; i < halfLength; i++) {
        let black = blackWhiteData[i];
        let red = redWhiteData[i];
        for (let j = 0; j < 8; j++) {
            let data;
            if ((red & 0x80) === 0) data = 0x04;
            else if ((black & 0x80) === 0) data = 0x00;
            else data = 0x03;
            data = (data << 4) & 0xFF;
            black = (black << 1) & 0xFF;
            red = (red << 1) & 0xFF;
            j++;
            if ((red & 0x80) === 0) data |= 0x04;
            else if ((black & 0x80) === 0) data |= 0x00;
            else data |= 0x03;
            black = (black << 1) & 0xFF;
            red = (red << 1) & 0xFF;
            payloadData[idx++] = data;
        }
    }
    return payloadData;
}

// ==================== APP模式专用函数 ====================
async function loadImageFromFile(file) {
    return new Promise((resolve, reject) => {
        const img = new Image();
        img.onload = () => resolve(img);
        img.onerror = reject;
        img.src = URL.createObjectURL(file);
    });
}


async function sendimgAppMode() {
    const epdIndex = parseInt(document.getElementById('abSelect')?.value || '1');
    const compressEnabled = document.getElementById('compressEnable')?.checked || false;
    const epdTypeVal = 0x06;  // 七色屏固定

    addLog(`🔄 APP模式发送开始 (模式: ${epdIndex})`);

    // 数据存在性检查（严格按照您的逻辑）
    if (epdIndex === 1) { // A面
        if (!storedImageDataA) {
            addLog("❌ A面数据为空，请先点击「从主画布同步到 A 面」");
            return;
        }
    } else if (epdIndex === 2) { // B面
        if (!storedImageDataB) {
            addLog("❌ B面数据为空，请先点击「从主画布同步到 B 面」");
            return;
        }
    } else if (epdIndex === 3) { // A&B同显
        if (!storedImageDataA) {
            addLog("❌ A面数据为空，请先点击「从主画布同步到 A 面」");
            return;
        }
    } else if (epdIndex === 7) { // A&B异显
        if (!storedImageDataA || !storedImageDataB) {
            addLog("❌ AB异显模式需要同时具备A面和B面数据，请分别同步");
            return;
        }
    } else {
        addLog("⚠️ 未知模式，默认为A面");
        if (!storedImageDataA) {
            addLog("❌ A面数据为空，请先同步A面");
            return;
        }
    }

    // 直接使用已同步的数据（已经过抖动处理）
    const sourceImageDataA = storedImageDataA;
    const sourceImageDataB = storedImageDataB;

    // 转换为设备数据格式（无需再次抖动）
    let dataA = null, dataB = null;
    try {
        if (sourceImageDataA) {
            dataA = EpdFormat.convertWithType(epdTypeVal, canvas.width, canvas.height, sourceImageDataA, findClosestColor);
        }
        if (sourceImageDataB) {
            dataB = EpdFormat.convertWithType(epdTypeVal, canvas.width, canvas.height, sourceImageDataB, findClosestColor);
        }
    } catch (e) {
        addLog("❌ 格式转换失败: " + e.message);
        console.error(e);
        return;
    }

    // 根据模式组合最终数据
    let finalData = null;
    if (epdIndex === 1) {
        finalData = dataA;
        addLog(`单面模式（A面）：发送 A 面数据，长度 ${dataA ? dataA.length : 0} 字节`);
    } else if (epdIndex === 2) {
        finalData = dataB;
        addLog(`单面模式（B面）：发送 B 面数据，长度 ${dataB ? dataB.length : 0} 字节`);
    } else if (epdIndex === 3) {
        finalData = dataA;
        addLog(`同显模式：发送 A 面数据，长度 ${dataA ? dataA.length : 0} 字节`);
    } else if (epdIndex === 7) {
        if (!dataA || !dataB) {
            addLog("❌ 异显模式数据转换失败，缺少A或B面数据");
            return;
        }
        finalData = new Uint8Array(dataA.length + dataB.length);
        finalData.set(dataA, 0);
        finalData.set(dataB, dataA.length);
        addLog(`异显模式：发送 A+B 面数据，总长度 ${finalData.length} 字节`);
    } else {
        addLog("⚠️ 未知模式，默认发送A面");
        finalData = dataA;
    }

    if (!finalData) {
        addLog("❌ 未生成有效的设备数据，请检查图像内容");
        return;
    }

    // 发送图片
    startTime = Date.now();
    const statusEl = document.getElementById("status");
    statusEl.parentElement.style.display = "block";

    try {
        AppProtocol.setEpdType(epdTypeVal);
        AppProtocol.setEpdIndex(epdIndex);
        AppProtocol.setCompress(compressEnabled);
        AppProtocol.setProgressCallback((sent, total) => {
            const elapsed = (Date.now() - startTime) / 1000;
            setStatus(`发送图片: ${sent}/${total} 包, 用时 ${elapsed.toFixed(1)}s`);
        });
        AppProtocol.setCompleteCallback(() => {
            if (bleDevice && bleDevice.gatt && bleDevice.gatt.connected) {
                addLog("✅ APP模式传输完成（刷新等待时间长, 请耐心等待设备刷新）");
            }
        });

        addLog(`准备发送图片，模式: 七色, 压缩: ${compressEnabled}, 驱动: 0x${epdTypeVal.toString(16)}`);
        await AppProtocol.sendFullImage(finalData, 'sevenColor', epdTypeVal, compressEnabled);
        const elapsed = (Date.now() - startTime) / 1000;
        addLog(`✅ APP 模式发送完成！耗时: ${elapsed.toFixed(2)}s`);
    } catch (e) {
        addLog(`❌ APP 模式发送失败: ${e.message}`);
        console.error(e);
    } finally {
        updateButtonStatus();
        setTimeout(() => { statusEl.parentElement.style.display = "none"; }, 5000);
    }
}

//交错处理抖动好的数据
/**
 * JD79660 屏幕数据交错重排函数
 * 适配tsl0922驱动 3.98寸 768x552屏幕
 * 逻辑行552行(0~551)，上下各276行交错映射物理行
 * @param {Uint8Array} rawData 原始未重排四色图像数据，每字节4像素
 * @returns {Uint8Array} 交错重排完成后的图像数据
 */
function JD79660JiaoCuoYuChuLi(rawData) {
    // 1. 获取当前画布尺寸 匹配 canvasSizes 中 3.98_768_552
    const sizeItem = canvasSizes.find(item => item.name === "3.98_768_552");
    const W = sizeItem.width;  // 768
    const H = sizeItem.height; // 552
    const lineByteCount = W / 4; // 单行字节数 768/4=192
    const halfLineCount = H / 2;   // 上下两半各276行

    // 分配输出缓冲区，总长度和原始数据一致 W*H/4
    const interleaveBuf = new Uint8Array(rawData.length);
    addLog("TSL0922大佬的A0交错预处理!接收端不处理.");

    // 遍历每一行逻辑行 (0 ~ 551)
    for (let logicRow = 0; logicRow < H; logicRow++) {
        // 计算当前逻辑行在原始数组的起始偏移
        const rawLineOffset = logicRow * lineByteCount;
        // 计算映射后的物理行
        let physicalRow;
        if (logicRow < halfLineCount) {
            // 上半部分0~275 → 偶数物理行 0,2,4...550
            physicalRow = logicRow * 2;
        } else {
            // 下半部分276~551 → 反向奇数行 551,549...1
            const offset = logicRow - halfLineCount;
            physicalRow = (H - 1) - 2 * offset;
        }
        // 物理行对应输出缓冲区偏移
        const targetOffset = physicalRow * lineByteCount;
        // 复制单行全部字节到交错缓冲区对应位置
        for (let b = 0; b < lineByteCount; b++) {
            interleaveBuf[targetOffset + b] = rawLineOffset + b < rawData.length ? rawData[rawLineOffset + b] : 0;
        }
    }
    return interleaveBuf;
}


// 在全局定义一个 Promise 的 resolver
let readyResolver = null;

function waitForReady() {
    return new Promise((resolve) => {
        readyResolver = resolve;
        // 超时保护（如 30 秒）
        setTimeout(() => {
            if (readyResolver) {
                readyResolver();
                readyResolver = null;
                addLog("⚠️ 等待 ready=1 超时，强制继续");
            }
        }, 30000);
    });
}

// ==================== 发送图片（支持三协议）====================
async function sendimg(options = {}) {
    if (cropManager.isCropMode()) {
        alert("请先完成图片裁剪！发送已取消。");
        return;
    }

    if (appModeEnabled) {
        await sendimgAppMode();
        return;
    }

    // ---- Web 模式 ----
    const hasSpecialContent = paintManager && (
        (paintManager.scheduleData && paintManager.scheduleData.length > 0) ||
        (paintManager.todoData && paintManager.todoData.length > 0) ||
        paintManager.cardData ||
        paintManager.wifiData
    );
    if (hasSpecialContent) {
        addLog("特殊内容发送：重绘画布（禁用抖动/对比度，直接按渲染结果发送）");
        paintManager.redrawAll();
    } else {
        if (typeof convertDithering === 'function') convertDithering();
    }

    // 获取画布图像数据
    const canvasSizeVal = document.getElementById('canvasSize').value;
    const ditherMode = document.getElementById('ditherMode').value;
    const epdDriverSelect = document.getElementById('epddriver');
    const selectedOption = epdDriverSelect.options[epdDriverSelect.selectedIndex];

    if (selectedOption.getAttribute('data-size') !== canvasSizeVal && !confirm("警告：画布尺寸和驱动不匹配，是否继续？")) return;
    if (selectedOption.getAttribute('data-color') !== ditherMode && !confirm("警告：颜色模式和驱动不匹配，是否继续？")) return;

    startTime = Date.now();
    const statusEl = document.getElementById("status");
    statusEl.parentElement.style.display = "block";

    const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
    const processedData = processImageData(imageData, ditherMode);

    // ---- 槽位支持 ----
    const targetSlot = Number.isInteger(options.slot) ? options.slot : null;
    const noRefresh = options.noRefresh === true;   // 新增：是否禁止刷新

    if (targetSlot != null) {
        if (targetSlot < 0 || targetSlot >= slotState.count) {
            addLog(`无效的槽位编号：${targetSlot + 1}，当前槽位总数 ${slotState.count}`);
            return;
        }
        // 选择槽位
        if (!await write(EpdCmd.SET_SLOT, new Uint8Array([0, targetSlot]))) {
            addLog(`切换到槽位 ${targetSlot + 1} 失败。`);
            return;
        }
        // 缓存预览（在发送前）
        cacheCurrentSlotPreview(targetSlot, processedData, ditherMode);
    }

    updateButtonStatus(true);
    await write(EpdCmd.INIT);

    const useCRC = false;//(appVersion >= 0x20) && typeof BleTransfer !== 'undefined';
    const transferFn = useCRC ? writeImageCRC : writeImage;
    if (useCRC) addLog("使用CRC校验传输模式");

    // ---- 根据颜色模式发送 ----
    if (ditherMode === 'sixColor') {
        // 1. 获取画布原始六色索引 0黄,1绿,2蓝,3红,4黑,5白
        const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        const sixColorPalette = epdRealColors.sixColor;
        const indexArray = extractSixColorIndex(imageData, sixColorPalette);

        // 上位下标转硬件4bit码：0→2,1→6,2→5,3→3,4→0,5→1
        const hwMap = [2, 6, 5, 3, 0, 1];
        const mappedArray = new Uint8Array(indexArray.length);
        for (let i = 0; i < indexArray.length; i++) {
            mappedArray[i] = hwMap[indexArray[i]];
        }
        if ((canvas.width == 768 || canvas.width == 552) || (canvas.width == 792 || canvas.width == 528)) {
            //3.98寸屏幕的特殊处理，直接把映射后的索引数据交错成4bit数据，传给固件
            const firstData = mapSixColorToWaveform(mappedArray, canvas.width, canvas.height, true);
            const secondData = mapSixColorToWaveform(mappedArray, canvas.width, canvas.height, false);

            startTime = Date.now();
            const statusEl = document.getElementById("status");
            statusEl.parentElement.style.display = "block";
            updateButtonStatus(true);
            await write(EpdCmd.INIT);

            // ========== 第一阶段刷新 color_map 清屏-显示-红黄绿 ==========
            await transferFn(firstData, 'color');
            await write(EpdCmd.REFRESH);
            addLog("⏳ E6 第一阶段刷新( color_map )等待(ready=1)...");
            // 等待下位机发送 "ready=1" 通知
            await waitForReady();
            await sleep(1000);

            // ========== 第二阶段刷新 color_map1 显示-蓝黑==========
            await transferFn(secondData, 'blue');
            await write(EpdCmd.REFRESH);
        } else {

            // 原始E6 打包4bit原始数据（传给固件第一层输入）
            const rawData = packSixColorTo4bit(mappedArray, canvas.width, canvas.height);

            startTime = Date.now();
            const statusEl = document.getElementById("status");
            statusEl.parentElement.style.display = "block";
            updateButtonStatus(true);
            await write(EpdCmd.INIT);

            // ========== 第一阶段刷新 color_map ==========
            await transferFn(rawData, 'color');
            await write(EpdCmd.REFRESH);
            //addLog("⏳ E6 第一阶段刷新( color_map )等待10秒...");
            //await sleep(10000);
            addLog("⏳ E6 第一阶段刷新( color_map )等待(ready=1)...");
            // 等待下位机发送 "ready=1" 通知
            await waitForReady();
            await sleep(1000);

            // ========== 第二阶段刷新 color_map1 ==========
            await transferFn(rawData, 'color');
            await write(EpdCmd.REFRESH);
        }

        updateButtonStatus();
        const elapsed = (Date.now() - startTime) / 1000;
        addLog(`✅ E6 双阶段传输完成！耗时: ${elapsed}s`);
        setStatus(`✅ E6 传输完成！耗时: ${elapsed}s`);
        setTimeout(() => { statusEl.parentElement.style.display = "none"; }, 5000);
        return;
    } else if (ditherMode === 'fourColor') {
        await transferFn(processedData, 'color');
    } else if (ditherMode === 'threeColor') {
        const half = Math.floor(processedData.length / 2);
        const bwData = processedData.slice(0, half);
        const redData = processedData.slice(half);
        if (epdDriverSelect.value === '08' || epdDriverSelect.value === '09') {
            await transferFn(convertUC8159(bwData, redData), 'bw');
        } else {
            await transferFn(bwData, 'bw');
            await transferFn(redData, 'red');
        }
    } else if (ditherMode === 'blackWhiteColor') {
        if (epdDriverSelect.value === '08' || epdDriverSelect.value === '09') {
            const empty = new Uint8Array(processedData.length).fill(0xFF);
            await transferFn(convertUC8159(processedData, empty), 'bw');
        } else {
            await transferFn(processedData, 'bw');
        }
    } else {
        addLog("当前固件不支持此颜色模式。");
        updateButtonStatus();
        return;
    }

    // ---- 刷新控制 ----
    if (noRefresh && targetSlot !== null) {
        if(document.getElementById("driverPreset").value == "GuoWangYanYu"){
            await write(EpdCmd.REFRESH);
            addLog(`✅ 图片数据已存入槽位 ${targetSlot + 1}，等待刷新...`);
            
        }else{
            // 发送完成标记，告知下位机结束当前槽位上载 //东山驱动专用
            await write(EpdCmd.WRITE_IMG, new Uint8Array([0xFF]));
            // 仅发送数据，不刷新
            addLog(`✅ 图片数据已存入槽位 ${targetSlot + 1}，未刷新屏幕。`);
            setStatus(`存入完成，未刷新屏幕。`);
        }
        imageTransferActive = false;
        updateButtonStatus();
        setTimeout(() => { statusEl.parentElement.style.display = "none"; }, 5000);
        return;
    }

    // ---- 正常刷新流程 ----
    addLog('图片数据发送完成，等待屏幕刷新...');
    setStatus('图片数据发送完成，正在刷新屏幕...');
    startImageRefreshWait();

    if (!await write(EpdCmd.REFRESH)) {
        cancelImageRefreshWait();
        setStatus('❌ 刷新命令发送失败。');
        imageTransferActive = false;
        updateButtonStatus();
        return;
    }
    await write(EpdCmd.REFRESH);
    updateButtonStatus();

    const elapsed = (Date.now() - startTime) / 1000;
    addLog(`发送完成！耗时: ${elapsed}s`);
    setStatus(`发送完成！耗时: ${elapsed}s`);
    addLog("屏幕刷新完成前请不要操作。");
    setTimeout(() => {
        statusEl.parentElement.style.display = "none";
    }, 5000);
}

// ==================== 下载/上传数组 ====================
function downloadDataArray() {
    if (cropManager.isCropMode()) {
        alert("请先完成图片裁剪！下载已取消。");
        return;
    }

    const hasSpecial = paintManager && (
        (paintManager.scheduleData && paintManager.scheduleData.length > 0) ||
        (paintManager.todoData && paintManager.todoData.length > 0) ||
        paintManager.cardData ||
        paintManager.wifiData
    );
    if (hasSpecial) {
        addLog("特殊内容下载：重绘画布（禁用抖动/对比度，直接导出PCF渲染结果）");
        paintManager.redrawAll();
    }

    const mode = document.getElementById('ditherMode').value;
    const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
    const processedData = processImageData(imageData, mode);

    const hexLines = [];
    for (let i = 0; i < processedData.length; i++) {
        hexLines.push("0x" + (processedData[i] & 0xFF).toString(16).padStart(2, '0'));
    }
    const chunks = [];
    for (let i = 0; i < hexLines.length; i += 16) {
        chunks.push(hexLines.slice(i, i + 16).join(', '));
    }

    const colorModeCode = mode === 'sevenColor' ? 7 : mode === 'sixColor' ? 6 : mode === 'fourColor' ? 4 : mode === 'threeColor' ? 3 : mode === 'blackWhiteColor' ? 2 : 3;
    const content = [
        'const uint8_t imageData[] PROGMEM = {',
        chunks.join(',\n'),
        '};',
        `const uint16_t imageWidth = ${canvas.width};`,
        `const uint16_t imageHeight = ${canvas.height};`,
        `const uint8_t colorMode = ${colorModeCode};`
    ].join('\n');

    const blob = new Blob([content], { type: 'text/plain' });
    const link = document.createElement('a');
    link.download = 'imagedata.h';
    link.href = URL.createObjectURL(blob);
    link.click();
    URL.revokeObjectURL(link.href);
}

function downloadImage() {
    // 将当前 canvas 内容保存为 PNG 文件，尺寸保持原样
    const link = document.createElement('a');
    link.download = 'epd_image.png';
    link.href = canvas.toDataURL('image/png');
    link.click();
}

function uploadDataArray() {
    if (cropManager.isCropMode()) {
        alert("请先完成图片裁剪！上传已取消。");
        return;
    }

    const fileInput = document.createElement('input');
    fileInput.type = 'file';
    fileInput.accept = '.h';
    fileInput.style.display = 'none';
    document.body.appendChild(fileInput);

    fileInput.addEventListener('change', function(e) {
        const file = e.target.files[0];
        if (!file) {
            document.body.removeChild(fileInput);
            return;
        }

        const reader = new FileReader();
        reader.onload = function(ev) {
            try {
                const content = ev.target.result;
                const widthMatch = content.match(/const uint16_t imageWidth\s*=\s*(\d+);/);
                const heightMatch = content.match(/const uint16_t imageHeight\s*=\s*(\d+);/);
                const colorModeMatch = content.match(/const uint8_t colorMode\s*=\s*(\d+);/);
                const dataMatch = content.match(/const uint8_t imageData\[\]\s+PROGMEM\s*=\s*\{([^}]+)\}/s);

                if (!widthMatch || !heightMatch || !colorModeMatch || !dataMatch) {
                    alert("无法解析数组文件，请确保文件格式与下载的一致。");
                    return;
                }

                const width = parseInt(widthMatch[1], 10);
                const height = parseInt(heightMatch[1], 10);
                const code = parseInt(colorModeMatch[1], 10);
                let modeStr;
                if (code === 7) modeStr = "sevenColor";
                else if (code === 6) modeStr = "sixColor";
                else if (code === 4) modeStr = "fourColor";
                else if (code === 2) modeStr = "blackWhiteColor";
                else if (code === 3) modeStr = "threeColor";
                else throw new Error("未知颜色模式码");

                const dataStr = dataMatch[1].replace(/\s+/g, '');
                const numbers = dataStr.split(',').filter(s => s.length).map(s => {
                    s = s.trim();
                    if (s.startsWith('0x') || s.startsWith('0X')) return parseInt(s.substring(2), 16);
                    return parseInt(s, 10);
                });
                const dataArray = new Uint8Array(numbers);

                let expected;
                if (modeStr === "sixColor") expected = width * height;
                else if (modeStr === "fourColor") expected = Math.ceil(width * height / 4);
                else if (modeStr === "threeColor") expected = Math.ceil(width * height / 8) * 2;
                else expected = Math.ceil(width * height / 8);
                if (dataArray.length !== expected) {
                    alert(`数组长度不匹配：预期 ${expected} 字节，实际 ${dataArray.length} 字节。`);
                    return;
                }

                canvas.width = width;
                canvas.height = height;
                const sizeSelect = document.getElementById('canvasSize');
                if (sizeSelect) {
                    const matchOpt = Array.from(sizeSelect.options).find(opt => {
                        const [_, w, h] = opt.value.split('_');
                        return parseInt(w, 10) === width && parseInt(h, 10) === height;
                    });
                    if (matchOpt) sizeSelect.value = matchOpt.value;
                }
                document.getElementById('ditherMode').value = modeStr;

                const decoded = decodeProcessedData(dataArray, width, height, modeStr);
                ctx.putImageData(decoded, 0, 0);
                if (paintManager) {
                    paintManager.clearElements();
                    paintManager.saveToHistory();
                }
                addLog(`✅ 已从文件加载数组：${width}x${height}，模式：${modeStr}，共 ${dataArray.length} 字节`);
            } catch (err) {
                console.error(err);
                alert("解析文件时出错：" + err.message);
            } finally {
                document.body.removeChild(fileInput);
            }
        };
        reader.readAsText(file);
    });
    fileInput.click();
}

// ==================== UI 辅助 ====================
function updateButtonStatus(forceDisabled = false) {
    const connected = gattServer && gattServer.connected;
    const disabled = forceDisabled || !connected ? 'disabled' : null;
    document.getElementById("reconnectbutton").disabled = (gattServer && gattServer.connected) ? 'disabled' : null;
    document.getElementById("sendcmdbutton").disabled = disabled;
    document.getElementById("calendarmodebutton").disabled = disabled;
    document.getElementById("clockmodebutton").disabled = disabled;
    document.getElementById("clearscreenbutton").disabled = disabled;
    document.getElementById("sendimgbutton").disabled = disabled;
    document.getElementById("setDriverbutton").disabled = disabled;
    document.getElementById("syncholidaybutton").disabled = disabled;
    
    const hasMultiple = (slotState.usedMask & (slotState.usedMask - 1n)) !== 0n; // 至少2个有效槽位
    const randomDisabled = status || !hasMultiple ? 'disabled' : null;
    document.getElementById("randomSlotSlideButton").disabled = randomDisabled;
    
    const testBtn = document.querySelector('button[onclick="syncAndShowCalendar()"]');
    if(testBtn) testBtn.disabled = disabled;
    
    // ---- 新增槽位按钮状态 ----
    const slotDisabled = (forceDisabled || !connected || imageTransferActive || slotActionPending || slotReadState !== null) ? 'disabled' : null;
    const refreshBtn = document.getElementById('refreshSlotsButton');
    const eraseAllBtn = document.getElementById('eraseAllSlotsButton');
    const startSlideBtn = document.getElementById('startSlotSlideButton');
    const stopSlideBtn = document.getElementById('stopSlotSlideButton');
    if (refreshBtn) refreshBtn.disabled = slotDisabled;
    if (eraseAllBtn) eraseAllBtn.disabled = slotDisabled || slotState.usedMask === 0n ? 'disabled' : null;
    if (startSlideBtn) startSlideBtn.disabled = slotDisabled;
    if (stopSlideBtn) stopSlideBtn.disabled = slotDisabled;
    
    // 重新渲染槽位网格（以更新内部按钮状态）
    renderSlotGrid(forceDisabled || imageTransferActive || slotActionPending || slotReadState !== null);
}

function disconnect() {
    updateButtonStatus();
    resetVariables();
    addLog('已断开连接.');
    document.getElementById("connectbutton").innerHTML = '连接';
}

// ==================== 根据协议显示/隐藏功能区 ====================
function updateUIBasedOnProtocol() {
    const webOnlyIds = ['calendarmodebutton','clockmodebutton','clearscreenbutton','syncholidaybutton','importholidaybutton','holidayhelpbutton','testTimestamp','testYear','testMonth'];
    const appOnlyIds = ['abSelectGroup','compressOptionGroup','doubleImagePanel'];
    const protocolSpan = document.getElementById('protocolStatus');
    if (protocolSpan) {
        if (appModeEnabled) {
            protocolSpan.textContent = 'APP 模式';
            protocolSpan.style.color = '#4CAF50';
        } else {
            protocolSpan.textContent = '网页模式 (Web)';
            protocolSpan.style.color = '#2196F3';
        }
    }

    if (appModeEnabled) {
        // 隐藏 Web 特有功能
        webOnlyIds.forEach(id => {
            const el = document.getElementById(id);
            if (el) {
                if (el.tagName === 'BUTTON' || el.tagName === 'INPUT' || el.tagName === 'SELECT') {
                    el.disabled = true;
                } else {
                    el.style.display = 'none';
                }
            }
        });
        // 显示 APP 特有功能
        appOnlyIds.forEach(id => {
            const el = document.getElementById(id);
            if (el) el.style.display = '';
        });
        //显示图像颜色和抖动操作栏
        const imagePanel = document.getElementById('image-panel');
        const imageModeBtn = document.getElementById('image-mode');
        if (imagePanel && imagePanel.style.display === 'none') {
            imagePanel.style.display = '';
            if (imageModeBtn) imageModeBtn.classList.add('active');
        }

        // 查找包含 #testYear 的 .flex-container.debug 并隐藏（不使用 :has 选择器）
        const testYearElement = document.getElementById('testYear');
        if (testYearElement) {
            let container = testYearElement.closest('.flex-container.debug');
            if (container) container.style.display = 'none';
        }
        // 隐藏残影消除相关区域
        const ghostingCyclesElement = document.getElementById('ghostingCycles');
        if (ghostingCyclesElement) {
            let container = ghostingCyclesElement.closest('.flex-container.debug');
            if (container) container.style.display = 'none';
        }
    } else {
        // Web 模式：恢复所有功能
        webOnlyIds.forEach(id => {
            const el = document.getElementById(id);
            if (el) {
                if (el.tagName === 'BUTTON' || el.tagName === 'INPUT' || el.tagName === 'SELECT') {
                    el.disabled = false;
                } else {
                    el.style.display = '';
                }
            }
        });
        appOnlyIds.forEach(id => {
            const el = document.getElementById(id);
            if (el) el.style.display = 'none';
        });

        // 恢复假期测试区域
        const testYearElement = document.getElementById('testYear');
        if (testYearElement) {
            let container = testYearElement.closest('.flex-container.debug');
            if (container) container.style.display = '';
        }
        // 恢复残影消除区域
        const ghostingCyclesElement = document.getElementById('ghostingCycles');
        if (ghostingCyclesElement) {
            let container = ghostingCyclesElement.closest('.flex-container.debug');
            if (container) container.style.display = '';
        }
    }
    //增加对 APP 模式状态栏的显示
    const statusBar = document.getElementById('appModeStatusBar');
    if (statusBar) {
        if (appModeEnabled) {
            statusBar.style.display = 'block';
            statusBar.innerHTML = `📌 APP 模式：当前画布尺寸 ${canvas.width}x${canvas.height} | A面${storedImageDataA ? '已设置' : '未设置'} | B面${storedImageDataB ? '已设置' : '未设置'}`;
        } else {
            statusBar.style.display = 'none';
        }
    }
}

// ==================== 蓝牙连接相关（自动检测协议）====================
async function filterConnect() {
    await preConnect(true, true);
}

async function preConnect(useFilter = false, forceNew = false) {
    if (gattServer && gattServer.connected) {
    	if (bleDevice && bleDevice.gatt.connected) bleDevice.gatt.disconnect();
    	if (!forceNew) return; await sleep(300);
    }
    resetVariables();
    try {
        const filterInput = document.getElementById('blenamefilter');
        const filterValue = filterInput?.value.trim();
        if (filterInput) filterInput.blur();
        const options = {
        	optionalServices: [
        		'62750001-d828-918d-fb46-b6c11c675aec', 
        		'0000ff01-0000-1000-8000-00805f9b34fb'
        ] };
        if (useFilter && filterValue && filterValue.length > 0) {
            const prefix = filterValue.toUpperCase();
            options.filters = [{ namePrefix: 'NRF_EPD_' + prefix }, { namePrefix: 'EPD_' + prefix },{ namePrefix: 'YSBadge2'}];
            addLog(`按名称过滤: NRF_EPD_${prefix} 或 EPD_${prefix} 或 YSBadge2`);
        } else {
        	options.acceptAllDevices = true;
        }
        bleDevice = await navigator.bluetooth.requestDevice(options);
        addLog(`已选择设备: ${bleDevice.name || bleDevice.id}`);
    } catch (e) {
        if (e.name === 'NotFoundError' || (e.message && e.message.includes('User cancelled'))) addLog("已取消设备选择。");
        else {
        	console.error(e); 
        	if (e.message) addLog("requestDevice: " + e.message); 
        	addLog("请检查蓝牙是否已开启，且使用的浏览器支持蓝牙！建议使用以下浏览器：");
            addLog("• 电脑: Chrome/Edge");
            addLog("• Android: Chrome/Edge");
            addLog("• iOS: Bluefy 浏览器");
        }
        return;
    }
    bleDevice.addEventListener('gattserverdisconnected', disconnect);
    setTimeout(async () => { await connect(); }, 300);
}

async function reConnect() {
    if (bleDevice && bleDevice.gatt.connected) bleDevice.gatt.disconnect();
    resetVariables();
    addLog("正在重连");
    setTimeout(async () => { await connect(); }, 300);
}

async function connect() {
    if (!bleDevice || epdCharacteristic) return;
    try {
        addLog("正在连接: " + bleDevice.name);
        gattServer = await bleDevice.gatt.connect();
        addLog("  找到 GATT Server");

        // ---------- 1. 尝试 Web 协议 ----------
        let webProtocolOk = false;
        try {
            epdService = await gattServer.getPrimaryService('62750001-d828-918d-fb46-b6c11c675aec');
            addLog("  找到 EPD Service (Web 协议)");
            epdCharacteristic = await epdService.getCharacteristic('62750002-d828-918d-fb46-b6c11c675aec');
            addLog("  找到 RX Characteristic");
            txCharacteristic = await epdService.getCharacteristic('62750003-d828-918d-fb46-b6c11c675aec');
            addLog("  找到 TX Characteristic");

            await epdCharacteristic.startNotifications();
            epdCharacteristic.addEventListener('characteristicvaluechanged', (event) => {
                handleNotify(event.target.value, msgIndex++);
            });
            addLog("  通知已开启");
            await sleep(50);
            appModeEnabled = false;
            addLog("📡 协议模式: 网页模式");
            webProtocolOk = true;
        } catch (e) {
            addLog("Web 协议识别失败，尝试 APP 协议...");
            // 如果 Web 协议失败，但可能部分变量已赋值，清理一下
            epdCharacteristic = null;
            txCharacteristic = null;
            epdService = null;
        }

        // ---------- 2. 如果 Web 协议失败，尝试 APP 协议 ----------
        if (!webProtocolOk) {
            try {
                epdService = await gattServer.getPrimaryService('0000ff01-0000-1000-8000-00805f9b34fb');
                addLog("  找到 EPD Service (APP 协议)");
                cmdCharacteristic = await epdService.getCharacteristic('0000ff03-0000-1000-8000-00805f9b34fb');
                addLog("  找到 WriteCMD Characteristic (0000ff03)");
                epdCharacteristic = await epdService.getCharacteristic('0000ff02-0000-1000-8000-00805f9b34fb');
                addLog("  找到 WritePic Characteristic (0000ff02)");
                txCharacteristic = await epdService.getCharacteristic('0000ff04-0000-1000-8000-00805f9b34fb');
                addLog("  找到 Notify Characteristic (0000ff04)");

                try {
                    await txCharacteristic.startNotifications();
                    txCharacteristic.addEventListener('characteristicvaluechanged', (event) => {
                        handleNotify(event.target.value, msgIndex++);
                    });
                    addLog("  通知已开启");
                } catch(e2) {
                    addLog("  通知开启失败（不影响写操作）: " + e2.message);
                }

                appModeEnabled = true;
                addLog("📡 协议模式: APP 模式");

                if (typeof AppProtocol !== 'undefined') {
                    AppProtocol.setCharacteristics(cmdCharacteristic, epdCharacteristic);
                    AppProtocol.setNotifyCharacteristic(txCharacteristic);
                    AppProtocol.setLogCallback(addLog);

                    // MTU 协商
                    let actualMtu = 23;
                    try {
                        await gattServer.requestMTU(256);
                        addLog("  已请求 MTU=256");
                        await sleep(500);
                        if (gattServer.mtu) {
                            actualMtu = gattServer.mtu;
                            addLog(`  协商实际 MTU (gattServer.mtu) = ${actualMtu}`);
                        } else if (cmdCharacteristic.service.device.gatt && cmdCharacteristic.service.device.gatt.mtu) {
                            actualMtu = cmdCharacteristic.service.device.gatt.mtu;
                            addLog(`  协商实际 MTU (device.gatt.mtu) = ${actualMtu}`);
                        } else {
                            addLog(`  ⚠️ 无法获取实际 MTU，使用默认 23`);
                        }
                    } catch(mtuErr) {
                        addLog(`  MTU 协商失败: ${mtuErr.message}，使用默认 23`);
                    }
                    AppProtocol.setMtuSize(actualMtu);
                    addLog(`  ✅ APP模式数据包负载大小 = ${actualMtu - 3} 字节`);

                    // 强制设置七色屏驱动
                    const epdDriverSelect = document.getElementById('epddriver');
                    let option = Array.from(epdDriverSelect.options).find(opt => opt.value === 'FF');
                    if (!option) {
                        option = document.createElement('option');
                        option.value = 'FF';
                        option.setAttribute('data-color', 'sevenColor');
                        option.setAttribute('data-size', '7.3E6_800_480');
                        option.text = '7.3寸 (七色, Spectra 6)';
                        epdDriverSelect.appendChild(option);
                    }
                    epdDriverSelect.value = 'FF';
                    const ditherModeSelect = document.getElementById('ditherMode');
                    if (ditherModeSelect) ditherModeSelect.value = 'sevenColor';
                    const canvasSizeSelect = document.getElementById('canvasSize');
                    if (canvasSizeSelect) canvasSizeSelect.value = '7.3E6_800_480';
                    updateCanvasSize();
                    addLog("✅ APP 模式：已强制设置为七色 7.3 寸屏幕 (Spectra 6)");
                    AppProtocol.setEpdType(0x06);
                    const abSelect = document.getElementById('abSelect');
                    AppProtocol.setEpdIndex(abSelect ? parseInt(abSelect.value) : 1);
                    const compressCheck = document.getElementById('compressEnable');
                    AppProtocol.setCompress(compressCheck ? compressCheck.checked : false);
                    addLog("  AppProtocol 初始化完成");
                } else {
                    addLog("  警告：AppProtocol 未加载，APP 模式无法发送图片");
                }
            } catch (e2) {
                // 两种协议都失败
                throw new Error("无法识别设备协议，请确认设备固件是否支持");
            }
        }

        // ---------- 3. 更新 UI 和后续初始化 ----------
        updateUIBasedOnProtocol();

        if (!appModeEnabled) {
            // Web 协议：读取版本、初始化屏幕、自动读取槽位（但需容错）
            try {
                const versionData = await txCharacteristic.readValue();
                appVersion = versionData.getUint8(0);
                addLog(`固件版本: 0x${appVersion.toString(16)}`);
                addLog(`APP版本: v${APP_VERSION} (${APP_BUILD_DATE})`);
            } catch(e) {
                appVersion = 0x15;
                addLog("无法读取固件版本，假定为 0x15");
            }

            if (typeof BleTransfer !== 'undefined') BleTransfer.init();

            await sleep(200);  // 增加这一行
            // 初始化屏幕
            await write(EpdCmd.INIT);

            // ---- 自动读取槽位（容错处理，不影响主流程） ----
            try {
                await refreshSlots();
            } catch (slotErr) {
                addLog(`⚠️ 自动读取槽位失败（不影响使用）: ${slotErr.message}`);
            }

            // 版本过低警告
            if (appVersion < 0x16) {
                const oldURL = "https://tsl0922.github.io/EPD-nRF5/v1.5";
                alert("!!!注意!!!\n当前固件版本过低，可能无法正常使用部分功能，建议升级到最新版本。");
                if (confirm('是否访问旧版本上位机？')) location.href = oldURL;
                setTimeout(()=> addLog(`如遇到问题，可访问旧版本上位机: ${oldURL}`), 500);
            }
        } else {
            appVersion = 0x20;
            addLog("APP 模式：固件版本假定为 0x20");
        }

        document.getElementById("connectbutton").innerHTML = '断开';
        updateButtonStatus();
        addLog("✅ 连接成功，可以发送指令或图片");

    } catch (e) {
        console.error(e);
        if (e.message) addLog("connect: " + e.message);
        disconnect();
        return;
    }
}

function handleNotify(value, idx) {
    const data = new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
    const isImageInfo = data.length >= 4 && data[0] === 0x69 && data[1] === 0x6D &&
        data[2] === 0x67 && data[3] === 0x3D;
    if (slotReadState && slotReadState.expectedChunk && !isImageInfo) {
        receiveSlotChunk(data);
        return;
    }
    
    if (appModeEnabled) {
        // APP 模式不处理 Web 消息
        return;
    }

    // CRC 传输
    if (data.length >= 1 && (data[0] === 0xA0 || data[0] === 0xA1)) {
        if (typeof BleTransfer !== 'undefined') {
            BleTransfer.handleNotification(value);
        }
        return;
    }

    const isTextNotification = data.length > 0 && data.every(byte => byte >= 0x20 && byte <= 0x7E);
    if ((!isTextNotification && data.length === 14) || idx === 0) {
        addLog(`收到配置：${bytes2hex(data)}`);
        const epdpins = document.getElementById("epdpins");
        const epddriver = document.getElementById("epddriver");
        epdpins.value = bytes2hex(data.slice(0, 7));
        if (data.length > 10) epdpins.value += bytes2hex(data.slice(10, 11));
        currentPinsValue = epdpins.value.trim().toLowerCase();
        epddriver.value = bytes2hex(data.slice(7, 8));
        deviceDriverValue = bytes2hex(data.slice(7, 8));   // 新增：保存驱动值
        a0_fix = 0;
        displayErrorActive = false;
        updateDitcherOptions();
    } else {
        if (textDecoder == null) textDecoder = new TextDecoder();
        const msg = textDecoder.decode(data);
        // ---- 自动识别驱动作者（仅首次） ----
        if (!driverAuthorDetected) {
            let presetId = null;
            if (msg.includes('DONGSHAN')) {
                presetId = 'dongshan';
            } else if (msg.includes('GUOWANGYANYU')) {
                presetId = 'GuoWangYanYu';
            } else if (msg.includes('REG') || msg.includes('REGISTERED')) {
                presetId = 'tsl0922';
            }
            if (presetId) {
                applyDriverPresetAll(presetId);
                driverAuthorDetected = true;
                addLog(`✅ 自动识别驱动作者: ${DRIVER_PRESETS.find(p => p.id === presetId).name} 设备ID:${deviceDriverValue}`);
            }
        }
        if (!msg.startsWith('chunk=')) addLog(msg, '⇓');
        if (applySlotsMessage(msg)) {
            addLog('图片槽位状态已更新。');
        } else if (msg === 'ready=1') {
            completeImageRefresh();
            if (readyResolver) {
                readyResolver();
                readyResolver = null;
            }
        } else if (beginSlotImageRead(msg)) {
            addLog('开始接收槽位图片。');
        } else if (beginSlotChunk(msg)) {
            // The next notification contains the binary chunk.
        } else if (msg.startsWith('display_error=')) {
            handleDisplayError(msg.substring('display_error='.length));
        } else if (msg.startsWith('slot_error=')) {
            const errorMessage = `槽位操作失败：${msg.substring('slot_error='.length)}`;
            if (slotActionPending) setSlotActionPending(false);
            if (slotReadState) {
                failSlotImageRead(errorMessage);
            } else {
                const status = document.getElementById('slotReadStatus');
                status.hidden = false;
                status.textContent = errorMessage;
                addLog(errorMessage);
            }
        } else if (msg.startsWith('mtu=') && msg.length > 4) {
            const mtuParts = msg.substring(4).trim().split(/\s+/);
            const mtuSize = parseInt(mtuParts[0], 10);
            rleSupport = mtuParts.includes('rle=1');
            document.getElementById('mtusize').value = mtuSize;
            addLog(`MTU 已更新为: ${mtuSize}`);
            if (rleSupport) addLog('设备已启用 RLE 压缩传输。');
        } else if (msg.startsWith('t=') && msg.length > 2) {
            const t = parseInt(msg.substring(2)) + new Date().getTimezoneOffset() * 60;
            addLog(`远端时间: ${new Date(t * 1000).toLocaleString()}`);
            addLog(`本地时间: ${new Date().toLocaleString()}`);
        }
    }
}

// ==================== 日志和状态 ====================
function setStatus(text) {
    const el = document.getElementById("status");
    if (el) el.innerHTML = text;
}

function addLog(msg, action = '') {
    const logDiv = document.getElementById("log");
    if (!logDiv) return;
    const now = new Date();
    const timeStr = `${String(now.getHours()).padStart(2,'0')}:${String(now.getMinutes()).padStart(2,'0')}:${String(now.getSeconds()).padStart(2,'0')} `;
    const line = document.createElement('div');
    line.className = 'log-line';
    const timeSpan = document.createElement('span');
    timeSpan.className = 'time';
    timeSpan.textContent = timeStr;
    line.appendChild(timeSpan);
    if (action) {
        const actionSpan = document.createElement('span');
        actionSpan.className = 'action';
        actionSpan.innerHTML = action;
        line.appendChild(actionSpan);
    }
    line.appendChild(document.createTextNode(msg));
    logDiv.appendChild(line);
    logDiv.scrollTop = logDiv.scrollHeight;
    while (logDiv.childNodes.length > 200) logDiv.removeChild(logDiv.firstChild);
}

function clearLog() {
    const logDiv = document.getElementById("log");
    if (logDiv) logDiv.innerHTML = '';
}

// ==================== 画布操作 ====================
function fillCanvas(style) {
    ctx.fillStyle = style;
    ctx.fillRect(0, 0, canvas.width, canvas.height);
}

function setCanvasTitle(title) {
    const titleEl = document.querySelector('.canvas-title');
    if (titleEl) {
        titleEl.innerText = title;
        titleEl.style.display = title && title !== '' ? 'block' : 'none';
    }
}

function updateImage() {
    const fileInput = document.getElementById('imageFile');
    if (!fileInput.files.length) {
        fillCanvas('white');
        return;
    }
    const img = new Image();
    img.onload = () => {
        URL.revokeObjectURL(img.src);
        if (img.width / img.height === canvas.width / canvas.height) {
            if (cropManager.isCropMode()) cropManager.exitCropMode();
            ctx.drawImage(img, 0, 0, img.width, img.height, 0, 0, canvas.width, canvas.height);
            scheduleConvertDithering();
        } else {
            alert(`图片宽高比例与画布不匹配，将进入裁剪模式。\n请放大图片后移动图片使其充满画布, 再点击"完成"按钮。`);
            if (paintManager) paintManager.setActiveTool(null, '');
            cropManager.initializeCrop();
        }
    };
    img.src = URL.createObjectURL(fileInput.files[0]);
}

function updateCanvasSize() {
    const selected = document.getElementById('canvasSize').value;
    const size = canvasSizes.find(s => s.name === selected);
    canvas.width = size.width;
    canvas.height = size.height;
    updateImage();
}

function updateDitcherOptions() {
    const select = document.getElementById('epddriver');
    // 如果没有选择框或没有选项，直接返回
    if (!select || select.options.length === 0) return;

    // 确保 selectedIndex 有效
    let idx = select.selectedIndex;
    if (idx < 0 || idx >= select.options.length) {
        // 尝试根据 select.value 匹配
        const val = select.value;
        if (val) {
            for (let i = 0; i < select.options.length; i++) {
                if (select.options[i].value === val) {
                    select.selectedIndex = i;
                    break;
                }
            }
        }
        // 如果还是无效，强制选中第一个
        if (select.selectedIndex < 0 || select.selectedIndex >= select.options.length) {
            select.selectedIndex = 0;
        }
    }

    const opt = select.options[select.selectedIndex];
    // 极端情况下 opt 仍可能为 undefined，再防护一次
    if (!opt) return;

    const color = opt.getAttribute('data-color');
    const size = opt.getAttribute('data-size');
    if (color) document.getElementById('ditherMode').value = color;
    if (size) document.getElementById('canvasSize').value = size;
    updateCanvasSize();
}

function rotateCanvas() {
    const w = canvas.width, h = canvas.height;
    const imgData = ctx.getImageData(0, 0, w, h);
    canvas.width = h;
    canvas.height = w;
    const offCanvas = document.createElement('canvas');
    offCanvas.width = w;
    offCanvas.height = h;
    offCanvas.getContext('2d').putImageData(imgData, 0, 0);
    ctx.translate(canvas.width / 2, canvas.height / 2);
    ctx.rotate(90 * Math.PI / 180);
    ctx.drawImage(offCanvas, -w / 2, -h / 2);
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    if (paintManager) {
        paintManager.clearHistory();
        paintManager.clearElements();
        paintManager.saveToHistory();
    }
}

function clearCanvas() {
    if (!confirm('清除画布内容?')) return false;
    fillCanvas('white');
    if (paintManager) {
        paintManager.clearElements();
        if (cropManager.isCropMode()) cropManager.exitCropMode();
        paintManager.saveToHistory();
    }
    return true;
}

// ==================== 抖动处理（带防抖）====================
let _pendingDitherJob = null;

/**
 * 调整亮度（整体偏移）
 * @param {ImageData} imageData 图像数据
 * @param {number} brightness  亮度系数，范围 0.5～1.5，1.0 表示不变
 * @returns {ImageData} 处理后的图像数据
 */
function adjustBrightness(imageData, brightness) {
    const data = imageData.data;
    const offset = (brightness - 1) * 128;   // 亮度偏移量，范围 -64～+64
    if (Math.abs(offset) < 0.5) return imageData;
    for (let i = 0; i < data.length; i += 4) {
        data[i]     = Math.min(255, Math.max(0, data[i]     + offset));
        data[i + 1] = Math.min(255, Math.max(0, data[i + 1] + offset));
        data[i + 2] = Math.min(255, Math.max(0, data[i + 2] + offset));
    }
    return imageData;
}

function scheduleConvertDithering() {
    if (_pendingDitherJob) {
        if (_pendingDitherJob.type === 'idle' && typeof cancelIdleCallback === 'function') {
            cancelIdleCallback(_pendingDitherJob.id);
        } else if (_pendingDitherJob.type === 'raf') {
            cancelAnimationFrame(_pendingDitherJob.id);
        }
        _pendingDitherJob = null;
    }
    const doDither = () => {
        _pendingDitherJob = null;
        if (typeof convertDithering === 'function') convertDithering();
    };
    if (typeof requestIdleCallback === 'function') {
        _pendingDitherJob = { type: 'idle', id: requestIdleCallback(doDither, { timeout: 200 }) };
    } else {
        _pendingDitherJob = { type: 'raf', id: requestAnimationFrame(doDither) };
    }
}

/**
 * 对 ImageData 执行完整的预处理（对比度、亮度、抖动）
 * @param {ImageData} imageData 
 * @param {Object} options 可选覆盖参数，若不传则从 UI 读取
 * @returns {ImageData} 处理后的 ImageData
 */
function processImageDataWithUI(imageData, options = {}) {
    const contrast = options.contrast !== undefined ? options.contrast : parseFloat(document.getElementById('ditherContrast').value);
    const brightness = options.brightness !== undefined ? options.brightness : parseFloat(document.getElementById('ditherBrightness').value);
    const alg = options.alg || document.getElementById('ditherAlg').value;
    const strength = options.strength !== undefined ? options.strength : parseFloat(document.getElementById('ditherStrength').value);
    const colorMode = options.colorMode || document.getElementById('ditherMode').value;
    const useLegacy = document.getElementById('useLegacyDither')?.checked || false;
    
    let processed = new ImageData(new Uint8ClampedArray(imageData.data), imageData.width, imageData.height);
    if (!isNaN(contrast)) processed = adjustContrast(processed, contrast);
    if (!isNaN(brightness) && brightness !== 1.0) processed = adjustBrightness(processed, brightness);
    if (alg !== 'none') {
        // 注意：ditherImage 会直接修改传入的 imageData，我们传入一个副本
        processed = ditherImage(processed, alg, strength, colorMode);
    }
    return processed;
}
/**
 * 将当前主画布内容保存为指定面的 ImageData
 * @param {'A'|'B'} side 
 */
function syncCurrentCanvasToSide(side) {
    const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
    if (side === 'A') {
        storedImageDataA = imageData;
        document.getElementById('aStatusLabel').innerText = `已同步 (${canvas.width}x${canvas.height})`;
        addLog(`✅ 已将当前画布内容同步到 A 面（尺寸 ${canvas.width}x${canvas.height}）`);
        // 可选：更新预览（如果用户勾选了“实时预览”）
    } else {
        storedImageDataB = imageData;
        document.getElementById('bStatusLabel').innerText = `已同步 (${canvas.width}x${canvas.height})`;
        addLog(`✅ 已将当前画布内容同步到 B 面（尺寸 ${canvas.width}x${canvas.height}）`);
    }
    // 更新底部协议状态栏中的 A/B 面状态
    updateUIBasedOnProtocol();
    // 若处于 AB 异显模式，可自动勾选启用抖动（视觉反馈）
    const abSelect = document.getElementById('abSelect');
    if (abSelect && abSelect.value === '7') {
        document.getElementById('ditherEnable').checked = true;
    }
}

function convertDithering() {
	// 如果是特殊模式（课表、待办等），不进行抖动
    const hasSpecial = paintManager && (
        (paintManager.scheduleData && paintManager.scheduleData.length > 0) ||
        (paintManager.todoData && paintManager.todoData.length > 0) ||
        paintManager.cardData ||
        paintManager.wifiData
    );
    if (hasSpecial) {
        addLog("特殊模式：已禁用抖动/对比度调整（直接发送渲染结果）");
        return;
    }

    if (paintManager) {
        paintManager.redrawTextElements();
        paintManager.redrawLineSegments();
    }

    // 1. 获取当前画布数据
    const current = ctx.getImageData(0, 0, canvas.width, canvas.height);
    let imgData = new ImageData(new Uint8ClampedArray(current.data), current.width, current.height);
    // 2. 亮度调整
    const brightness = parseFloat(document.getElementById('ditherBrightness').value);
    if (!isNaN(brightness) && brightness !== 1.0) {
        imgData = adjustBrightness(imgData, brightness);
    }
    // 3. 对比度调整
    const contrast = parseFloat(document.getElementById('ditherContrast').value);
    if (!isNaN(contrast)) {
        imgData = adjustContrast(imgData, contrast);
    }
    //adjustContrast(imgData, contrast);
    // 4. 抖动处理
    const alg = document.getElementById('ditherAlg').value;
    const strength = parseFloat(document.getElementById('ditherStrength').value);
    const mode = document.getElementById('ditherMode').value;
    const processed = processImageData(ditherImage(imgData, alg, strength, mode), mode);
    const final = decodeProcessedData(processed, canvas.width, canvas.height, mode);
    ctx.putImageData(final, 0, 0);
    if (paintManager) paintManager.saveToHistory();
}

function applyDither() {
    cropManager.finishCrop(() => scheduleConvertDithering());
}

// ==================== 假期同步功能 ====================
async function loadHolidayJson(year) {
    try {
        const resp = await fetch(`holiday-cn/${year}.json`);
        if (resp.ok) {
            const data = await resp.json();
            addLog(`成功加载${year}年假期数据，共${data.days.length}条记录`);
            return data;
        } else {
            addLog(`未找到${year}年的假期数据文件 (HTTP ${resp.status})`);
            addLog(`请确认文件路径: holiday-cn/${year}.json`);
            return null;
        }
    } catch (e) {
        addLog("加载假期数据失败: " + e.message);
        if (e.message.includes('Failed to fetch')) {
            addLog("⚠️ 可能的原因:");
            addLog("  1. 请通过HTTP服务器访问此页面（而非file://协议）");
            addLog(`  2. 检查holiday-cn/${year}.json文件是否存在`);
        }
        return null;
    }
}

function convertJsonToDeviceFormat(holidayJson) {
    const codes = [];
    for (const day of holidayJson.days) {
        const [year, month, date] = day.date.split('-');
        const m = parseInt(month, 10);
        const d = parseInt(date, 10);
        const flag = day.isOffDay ? 0 : 1;
        codes.push((flag << 12) | (m << 8) | d);
    }
    return codes;
}

function validateHolidayJson(obj) {
    if (!obj || typeof obj !== 'object') return { ok: false, message: "JSON 为空或格式错误" };
    if (!Number.isInteger(obj.year) || obj.year < 2000 || obj.year > 2100) return { ok: false, message: "缺少有效的 year 字段" };
    if (!Array.isArray(obj.days)) return { ok: false, message: "缺少 days 数组" };
    for (const day of obj.days) {
        if (!day || typeof day !== 'object') return { ok: false, message: "days 中包含无效项" };
        if (typeof day.date !== 'string' || !/^\d{4}-\d{2}-\d{2}$/.test(day.date)) return { ok: false, message: "days.date 格式错误，应为 YYYY-MM-DD" };
        if (typeof day.isOffDay !== 'boolean') return { ok: false, message: "days.isOffDay 必须为布尔值" };
    }
    return { ok: true };
}

async function importHolidayJsonFile(file) {
    try {
        addLog("正在读取假期文件: " + file.name);
        const text = await file.text();
        const json = JSON.parse(text);
        const valid = validateHolidayJson(json);
        if (valid.ok) {
            const codes = convertJsonToDeviceFormat(json);
            await sendHolidayDataToDevice(json.year, codes, "导入文件: " + file.name);
        } else {
            alert("假期 JSON 校验失败：" + valid.message);
            addLog("❌ 假期 JSON 校验失败：" + valid.message);
        }
    } catch (e) {
        alert("读取或解析假期 JSON 失败：" + e.message);
        addLog("❌ 读取或解析假期 JSON 失败：" + e.message);
    }
}

async function sendHolidayDataToDevice(year, codes, source) {
    if (codes.length === 0) {
        alert("没有有效的假期数据！");
        return;
    }
    if (codes.length > 128) {
        alert("假期数据过多，最多支持128个！");
        return;
    }
    if (!confirm(`即将同步${year}年的假期数据到设备\n共${codes.length}个假期/调休日\n数据来源: ${source}\n\n确认继续？`)) {
        addLog("用户取消了同步操作");
        return;
    }
    const buf = new Uint8Array(3 + codes.length * 2);
    buf[0] = (year >> 8) & 0xFF;
    buf[1] = year & 0xFF;
    buf[2] = codes.length;
    for (let i = 0; i < codes.length; i++) {
        buf[3 + i * 2] = (codes[i] >> 8) & 0xFF;
        buf[3 + i * 2 + 1] = codes[i] & 0xFF;
    }
    addLog(`正在发送 ${year} 年假期数据，共 ${codes.length} 个假期...`);
    const success = await write(EpdCmd.SET_HOLIDAYS, buf);
    if (success) {
        addLog("✅ 假期数据已成功同步到设备！");
        addLog("✔ 数据已保存到设备，断电不丢失");
    } else {
        addLog("❌ 假期数据发送失败！");
    }
}

async function syncHolidayData() {
    const year = new Date().getFullYear();
    addLog(`正在加载${year}年的假期数据...`);
    const json = await loadHolidayJson(year);
    if (json) {
        await sendHolidayDataToDevice(year, convertJsonToDeviceFormat(json), "holiday-cn");
    } else {
        alert(`无法加载${year}年的假期数据！\n请确认 holiday-cn/${year}.json 文件存在。`);
    }
}

function showHolidayHelp() {
    document.getElementById("holidayHelpDialog").style.display = "block";
    document.getElementById("holidayHelpOverlay").style.display = "block";
}
function closeHolidayHelp() {
    document.getElementById("holidayHelpDialog").style.display = "none";
    document.getElementById("holidayHelpOverlay").style.display = "none";
}

async function syncAndShowCalendar() {
    const year = parseInt(document.getElementById("testYear").value);
    const month = parseInt(document.getElementById("testMonth").value);
    const info = document.getElementById("holidayTestInfo");
    if (!year || year < 2007 || year > 2050) {
        alert("请输入有效的年份 (2007-2050)");
        return;
    }
    if (!month || month < 1 || month > 12) {
        alert("请选择有效的月份 (1-12)");
        return;
    }
    addLog(`=== 假期日历测试: ${year}年${month}月 ===`);
    info.textContent = `正在加载 ${year} 年数据...`;
    const json = await loadHolidayJson(year);
    if (!json) {
        info.textContent = `❌ 未找到 ${year} 年数据`;
        alert(`无法加载${year}年的假期数据！\n请确认 holiday-cn/${year}.json 文件存在。`);
        return;
    }
    const codes = convertJsonToDeviceFormat(json);
    if (codes.length === 0) {
        info.textContent = `⚠️ ${year} 年无假期数据`;
        addLog(`警告: ${year}年没有假期数据`);
    } else {
        info.textContent = `✅ 已加载 ${codes.length} 个假期`;
    }
    const buf = new Uint8Array(3 + codes.length * 2);
    buf[0] = (year >> 8) & 0xFF;
    buf[1] = year & 0xFF;
    buf[2] = codes.length;
    for (let i = 0; i < codes.length; i++) {
        buf[3 + i * 2] = (codes[i] >> 8) & 0xFF;
        buf[3 + i * 2 + 1] = codes[i] & 0xFF;
    }
    addLog(`发送 ${year} 年假期数据 (${codes.length} 个)...`);
    if (await write(EpdCmd.SET_HOLIDAYS, buf)) {
        addLog("✅ 假期数据已发送");
        const targetDate = new Date(year, month - 1, 1, 0, 0, 0);
        const timestamp = Math.floor(targetDate.getTime() / 1000);
        addLog(`设置日期到: ${year}-${String(month).padStart(2,'0')}-01`);
        const timeData = new Uint8Array([
            (timestamp >> 24) & 0xFF, (timestamp >> 16) & 0xFF,
            (timestamp >> 8) & 0xFF, timestamp & 0xFF,
            -(new Date().getTimezoneOffset() / 60),
            1
        ]);
        if (await write(EpdCmd.SET_TIME, timeData)) {
            addLog(`✅ 已设置到 ${year}年${month}月，切换到日历模式`);
            addLog(`📅 设备将显示 ${year}年${month}月的日历和调休信息`);
            addLog("⏳ 屏幕刷新完成前请不要操作");
            info.textContent = `✅ 显示 ${year}年${month}月日历`;
            const monthCodes = codes.filter(c => ((c >> 8) & 0x0F) === month);
            if (monthCodes.length > 0) {
                const rest = monthCodes.filter(c => ((c >> 12) & 0x0F) === 0).length;
                const work = monthCodes.filter(c => ((c >> 12) & 0x0F) === 1).length;
                addLog(`📊 ${month}月: ${rest}个休息日, ${work}个调休上班日`);
            } else {
                addLog(`📊 ${month}月: 无特殊假期安排`);
            }
        } else {
            info.textContent = "❌ 切换日历失败";
            addLog("❌ 切换到日历模式失败！");
        }
    } else {
        info.textContent = "❌ 假期数据发送失败";
        addLog("❌ 假期数据发送失败！");
    }
}

// ==================== 测试时间戳功能 ====================
function setCurrentTimestamp() {
    const now = Math.floor(Date.now() / 1000);
    document.getElementById("testTimestamp").value = now;
    updateTimestampInfo();
}
function addDays(delta) {
    const input = document.getElementById("testTimestamp");
    let val = parseInt(input.value);
    if (isNaN(val)) val = Math.floor(Date.now() / 1000);
    input.value = val + delta * 86400;
    updateTimestampInfo();
}
function updateTimestampInfo() {
    const ts = parseInt(document.getElementById("testTimestamp").value);
    const info = document.getElementById("timestampInfo");
    if (isNaN(ts) || ts <= 0) {
        info.textContent = "";
        return;
    }
    const d = new Date(ts * 1000);
    const y = d.getFullYear();
    const m = String(d.getMonth() + 1).padStart(2,'0');
    const day = String(d.getDate()).padStart(2,'0');
    const h = String(d.getHours()).padStart(2,'0');
    const min = String(d.getMinutes()).padStart(2,'0');
    const s = String(d.getSeconds()).padStart(2,'0');
    const week = ["日","一","二","三","四","五","六"][d.getDay()];
    info.textContent = `对应时间: ${y}-${m}-${day} 星期${week} ${h}:${min}:${s}`;
}
async function testCalendarJump(mode) {
    const ts = parseInt(document.getElementById("testTimestamp").value);
    if (isNaN(ts) || ts <= 0) {
        alert("请输入有效的时间戳（Unix时间戳，秒为单位）");
        return;
    }
    const localStr = new Date(ts * 1000).toLocaleString("zh-CN");
    const modeName = mode === 1 ? "日历" : "时钟";
    if (!confirm(`确认要将设备时间设置为:\n${localStr}\n并切换到${modeName}模式?`)) return;
    const data = new Uint8Array([
        (ts >> 24) & 0xFF, (ts >> 16) & 0xFF, (ts >> 8) & 0xFF, ts & 0xFF,
        -(new Date().getTimezoneOffset() / 60),
        mode
    ]);
    if (await write(EpdCmd.SET_TIME, data)) {
        addLog("测试时间已设置: " + localStr);
        addLog(`模式: ${modeName}模式`);
        addLog("屏幕刷新完成前请不要操作。");
    }
}

// ==================== 编辑器初始化（保持不变）====================
function initImageEditor() {
    const imageModeBtn = document.getElementById('image-mode');
    const imagePanel = document.getElementById('image-panel');
    const schedulePanel = document.getElementById('schedule-panel');
    const todoPanel = document.getElementById('todo-panel');
    const cardPanel = document.getElementById('card-panel');
    const wifiPanel = document.getElementById('wifi-panel');
    const scheduleModeBtn = document.getElementById('schedule-mode');
    const todoModeBtn = document.getElementById('todo-mode');
    const cardModeBtn = document.getElementById('card-mode');
    const wifiModeBtn = document.getElementById('wifi-mode');

    if (imageModeBtn && imagePanel) {
        imageModeBtn.addEventListener('click', () => {
            const visible = imagePanel.style.display !== 'none';
            imagePanel.style.display = visible ? 'none' : '';
            imageModeBtn.classList.toggle('active', !visible);
            if (!visible) {
                if (schedulePanel) schedulePanel.style.display = 'none';
                if (todoPanel) todoPanel.style.display = 'none';
                if (cardPanel) cardPanel.style.display = 'none';
                if (wifiPanel) wifiPanel.style.display = 'none';
                if (scheduleModeBtn) scheduleModeBtn.classList.remove('active');
                if (todoModeBtn) todoModeBtn.classList.remove('active');
                if (cardModeBtn) cardModeBtn.classList.remove('active');
                if (wifiModeBtn) wifiModeBtn.classList.remove('active');
                if (paintManager) {
                    paintManager.scheduleData = null;
                    paintManager.todoData = null;
                    paintManager.cardData = null;
                    paintManager.wifiData = null;
                    paintManager.redrawAll();
                }
            }
        });
    }
}

function initScheduleEditor() {
    const scheduleModeBtn = document.getElementById('schedule-mode');
    const schedulePanel = document.getElementById('schedule-panel');
    const imagePanel = document.getElementById('image-panel');
    const todoPanel = document.getElementById('todo-panel');
    const cardPanel = document.getElementById('card-panel');
    const wifiPanel = document.getElementById('wifi-panel');
    const imageModeBtn = document.getElementById('image-mode');
    const todoModeBtn = document.getElementById('todo-mode');
    const cardModeBtn = document.getElementById('card-mode');
    const wifiModeBtn = document.getElementById('wifi-mode');
    const createBtn = document.getElementById('create-schedule-btn');
    const syncBtn = document.getElementById('schedule-sync-btn');
    const clearBtn = document.getElementById('schedule-clear-btn');
    const daysSelect = document.getElementById('schedule-days');
    const classesSelect = document.getElementById('schedule-classes');
    const fontSizeSelect = document.getElementById('schedule-font-size');

    if (scheduleModeBtn && schedulePanel) {
        scheduleModeBtn.addEventListener('click', () => {
            const visible = schedulePanel.style.display !== 'none';
            schedulePanel.style.display = visible ? 'none' : '';
            scheduleModeBtn.classList.toggle('active', !visible);
            if (!visible) {
                if (imagePanel) imagePanel.style.display = 'none';
                if (todoPanel) todoPanel.style.display = 'none';
                if (cardPanel) cardPanel.style.display = 'none';
                if (wifiPanel) wifiPanel.style.display = 'none';
                if (imageModeBtn) imageModeBtn.classList.remove('active');
                if (todoModeBtn) todoModeBtn.classList.remove('active');
                if (cardModeBtn) cardModeBtn.classList.remove('active');
                if (wifiModeBtn) wifiModeBtn.classList.remove('active');
                if (paintManager) {
                    paintManager.todoData = null;
                    paintManager.cardData = null;
                    paintManager.wifiData = null;
                    paintManager.redrawAll();
                }
            } else {
                if (typeof renderScheduleEditorTable === 'function') renderScheduleEditorTable();
            }
        });
    }

    if (createBtn) createBtn.addEventListener('click', async () => {
        const editor = document.getElementById('schedule-editor');
        if (editor) editor.style.display = 'none';
        const imagePanel = document.getElementById('image-panel');
        if (imagePanel) imagePanel.style.display = 'none';
        const imageModeBtn = document.getElementById('image-mode');
        if (imageModeBtn) imageModeBtn.classList.remove('active');
        if (paintManager) await paintManager.createSchedule();
        if (typeof renderScheduleEditorTable === 'function') renderScheduleEditorTable();
    });
    if (syncBtn) syncBtn.addEventListener('click', async () => {
        if (typeof syncScheduleToEPD === 'function') await syncScheduleToEPD();
    });
    if (clearBtn) clearBtn.addEventListener('click', () => {
        if (typeof clearScheduleEditorInputs === 'function') clearScheduleEditorInputs();
        if (paintManager && paintManager.scheduleData && paintManager.scheduleData.length) {
            for (let i = 1; i < paintManager.scheduleData.length; i++) {
                for (let j = 1; j < paintManager.scheduleData[i].length; j++) {
                    paintManager.scheduleData[i][j] = "";
                }
            }
            paintManager.redrawAll();
            paintManager.saveToHistory();
        }
    });
    const update = () => { if (typeof renderScheduleEditorTable === 'function') renderScheduleEditorTable(); };
    if (daysSelect) daysSelect.addEventListener('change', update);
    if (classesSelect) classesSelect.addEventListener('change', update);
    if (fontSizeSelect) fontSizeSelect.addEventListener('change', update);
}

function initTodoEditor() {
    const todoModeBtn = document.getElementById('todo-mode');
    const todoPanel = document.getElementById('todo-panel');
    const cardPanel = document.getElementById('card-panel');
    const wifiPanel = document.getElementById('wifi-panel');
    const schedulePanel = document.getElementById('schedule-panel');
    const imagePanel = document.getElementById('image-panel');
    const imageModeBtn = document.getElementById('image-mode');
    const scheduleModeBtn = document.getElementById('schedule-mode');
    const cardModeBtn = document.getElementById('card-mode');
    const wifiModeBtn = document.getElementById('wifi-mode');
    const createBtn = document.getElementById('create-todo-btn');
    const syncBtn = document.getElementById('todo-sync-btn');
    const clearBtn = document.getElementById('todo-clear-btn');
    const countSelect = document.getElementById('todo-count');
    const fontSizeSelect = document.getElementById('todo-font-size');

    if (todoModeBtn && todoPanel) {
        todoModeBtn.addEventListener('click', () => {
            const visible = todoPanel.style.display !== 'none';
            todoPanel.style.display = visible ? 'none' : '';
            todoModeBtn.classList.toggle('active', !visible);
            if (!visible) {
                if (cardPanel) cardPanel.style.display = 'none';
                if (wifiPanel) wifiPanel.style.display = 'none';
                if (schedulePanel) schedulePanel.style.display = 'none';
                if (imagePanel) imagePanel.style.display = 'none';
                if (cardModeBtn) cardModeBtn.classList.remove('active');
                if (wifiModeBtn) wifiModeBtn.classList.remove('active');
                if (scheduleModeBtn) scheduleModeBtn.classList.remove('active');
                if (imageModeBtn) imageModeBtn.classList.remove('active');
                if (paintManager) {
                    paintManager.scheduleData = null;
                    paintManager.cardData = null;
                    paintManager.wifiData = null;
                    paintManager.redrawAll();
                }
            } else {
                if (typeof renderTodoEditorTable === 'function') renderTodoEditorTable();
            }
        });
    }

    if (createBtn) createBtn.addEventListener('click', async () => {
        const editor = document.getElementById('todo-editor');
        if (editor) editor.style.display = 'none';
        const imagePanel = document.getElementById('image-panel');
        if (imagePanel) imagePanel.style.display = 'none';
        const imageModeBtn = document.getElementById('image-mode');
        if (imageModeBtn) imageModeBtn.classList.remove('active');
        if (paintManager) await paintManager.createTodoList();
        if (typeof renderTodoEditorTable === 'function') renderTodoEditorTable();
    });
    if (syncBtn) syncBtn.addEventListener('click', async () => {
        if (typeof syncTodoToEPD === 'function') await syncTodoToEPD();
    });
    if (clearBtn) clearBtn.addEventListener('click', () => {
        if (typeof clearTodoEditorInputs === 'function') clearTodoEditorInputs();
        if (paintManager && paintManager.todoData && paintManager.todoData.length) {
            paintManager.todoData.forEach(item => { item.text = ""; item.done = false; });
            paintManager.redrawAll();
            paintManager.saveToHistory();
        }
    });
    const update = () => { if (typeof renderTodoEditorTable === 'function') renderTodoEditorTable(); };
    if (countSelect) countSelect.addEventListener('change', update);
    if (fontSizeSelect) fontSizeSelect.addEventListener('change', update);
}

function initCardEditor() {
    const cardModeBtn = document.getElementById('card-mode');
    const cardPanel = document.getElementById('card-panel');
    const wifiPanel = document.getElementById('wifi-panel');
    const todoPanel = document.getElementById('todo-panel');
    const schedulePanel = document.getElementById('schedule-panel');
    const imagePanel = document.getElementById('image-panel');
    const imageModeBtn = document.getElementById('image-mode');
    const scheduleModeBtn = document.getElementById('schedule-mode');
    const todoModeBtn = document.getElementById('todo-mode');
    const wifiModeBtn = document.getElementById('wifi-mode');
    const syncBtn = document.getElementById('card-sync-btn');
    const clearBtn = document.getElementById('card-clear-btn');
    const inputs = ['card-name', 'card-title', 'card-phone', 'card-email', 'card-website', 'card-footer'];

    if (cardModeBtn && cardPanel) {
        cardModeBtn.addEventListener('click', () => {
            const visible = cardPanel.style.display !== 'none';
            cardPanel.style.display = visible ? 'none' : '';
            cardModeBtn.classList.toggle('active', !visible);
            if (!visible) {
                if (wifiPanel) wifiPanel.style.display = 'none';
                if (todoPanel) todoPanel.style.display = 'none';
                if (schedulePanel) schedulePanel.style.display = 'none';
                if (imagePanel) imagePanel.style.display = 'none';
                if (wifiModeBtn) wifiModeBtn.classList.remove('active');
                if (todoModeBtn) todoModeBtn.classList.remove('active');
                if (scheduleModeBtn) scheduleModeBtn.classList.remove('active');
                if (imageModeBtn) imageModeBtn.classList.remove('active');
                if (paintManager) {
                    paintManager.scheduleData = null;
                    paintManager.todoData = null;
                    paintManager.wifiData = null;
                    paintManager.redrawAll();
                }
            } else {
                if (typeof updateCardCanvasPreview === 'function') updateCardCanvasPreview({ saveHistory: false, onlyWhenPanelVisible: true });
            }
        });
    }

    if (syncBtn) syncBtn.addEventListener('click', async () => {
        if (typeof syncCardToEPD === 'function') await syncCardToEPD();
    });
    if (clearBtn) clearBtn.addEventListener('click', () => {
        inputs.forEach(id => {
            const el = document.getElementById(id);
            if (el) el.value = '';
        });
        if (paintManager && paintManager.cardData) {
            paintManager.cardData = null;
            paintManager.redrawAll();
            paintManager.saveToHistory();
        }
        if (typeof updateCardCanvasPreview === 'function') updateCardCanvasPreview({ saveHistory: false, onlyWhenPanelVisible: true });
    });
    inputs.forEach(id => {
        const el = document.getElementById(id);
        if (el) el.addEventListener('input', () => {
            if (typeof scheduleCardCanvasPreviewUpdate === 'function') scheduleCardCanvasPreviewUpdate();
        });
    });
    if (typeof scheduleCardCanvasPreviewUpdate === 'function') scheduleCardCanvasPreviewUpdate();
}

function initWifiEditor() {
    const wifiModeBtn = document.getElementById('wifi-mode');
    const wifiPanel = document.getElementById('wifi-panel');
    const todoPanel = document.getElementById('todo-panel');
    const cardPanel = document.getElementById('card-panel');
    const schedulePanel = document.getElementById('schedule-panel');
    const imagePanel = document.getElementById('image-panel');
    const imageModeBtn = document.getElementById('image-mode');
    const scheduleModeBtn = document.getElementById('schedule-mode');
    const todoModeBtn = document.getElementById('todo-mode');
    const cardModeBtn = document.getElementById('card-mode');
    const syncBtn = document.getElementById('wifi-sync');
    const clearBtn = document.getElementById('wifi-clear');
    const ssidInput = document.getElementById('wifi-ssid');
    const passInput = document.getElementById('wifi-password');
    const encSelect = document.getElementById('wifi-encryption');
    const hiddenCheck = document.getElementById('wifi-hidden');

    if (wifiModeBtn && wifiPanel) {
        wifiModeBtn.addEventListener('click', () => {
            const visible = wifiPanel.style.display !== 'none';
            wifiPanel.style.display = visible ? 'none' : '';
            wifiModeBtn.classList.toggle('active', !visible);
            if (!visible) {
                if (todoPanel) todoPanel.style.display = 'none';
                if (cardPanel) cardPanel.style.display = 'none';
                if (schedulePanel) schedulePanel.style.display = 'none';
                if (imagePanel) imagePanel.style.display = 'none';
                if (todoModeBtn) todoModeBtn.classList.remove('active');
                if (cardModeBtn) cardModeBtn.classList.remove('active');
                if (scheduleModeBtn) scheduleModeBtn.classList.remove('active');
                if (imageModeBtn) imageModeBtn.classList.remove('active');
                if (paintManager) {
                    paintManager.scheduleData = null;
                    paintManager.todoData = null;
                    paintManager.cardData = null;
                    paintManager.redrawAll();
                }
            } else {
                if (typeof renderWifiQrPreview === 'function') renderWifiQrPreview();
                if (typeof scheduleWifiCanvasPreviewUpdate === 'function') scheduleWifiCanvasPreviewUpdate();
            }
        });
    }
    if (syncBtn) syncBtn.addEventListener('click', async () => {
        if (typeof syncWifiToEPD === 'function') await syncWifiToEPD();
        if (typeof renderWifiQrPreview === 'function') renderWifiQrPreview();
        if (typeof scheduleWifiCanvasPreviewUpdate === 'function') scheduleWifiCanvasPreviewUpdate();
    });
    if (clearBtn) clearBtn.addEventListener('click', () => {
        if (ssidInput) ssidInput.value = '';
        if (passInput) passInput.value = '';
        if (encSelect) encSelect.value = 'WPA';
        if (hiddenCheck) hiddenCheck.checked = false;
        if (paintManager && paintManager.wifiData) {
            paintManager.wifiData = null;
            paintManager.redrawAll();
            paintManager.saveToHistory();
        }
        if (typeof renderWifiQrPreview === 'function') renderWifiQrPreview();
        if (typeof scheduleWifiCanvasPreviewUpdate === 'function') scheduleWifiCanvasPreviewUpdate();
    });

    const updateUI = () => {
        if (typeof renderWifiQrPreview === 'function') renderWifiQrPreview();
        if (typeof scheduleWifiCanvasPreviewUpdate === 'function') scheduleWifiCanvasPreviewUpdate();
    };
    if (ssidInput) ssidInput.addEventListener('input', updateUI);
    if (passInput) passInput.addEventListener('input', updateUI);
    if (encSelect) encSelect.addEventListener('change', updateUI);
    if (hiddenCheck) hiddenCheck.addEventListener('change', updateUI);
    if (typeof renderWifiQrPreview === 'function') renderWifiQrPreview();
    if (typeof scheduleWifiCanvasPreviewUpdate === 'function') scheduleWifiCanvasPreviewUpdate();
}

// 预览单张图片到主画布（应用当前抖动）
async function previewImageOnCanvas(file) {
    const img = await loadImageFromFile(file);
    const offCanvas = document.createElement('canvas');
    offCanvas.width = canvas.width;
    offCanvas.height = canvas.height;
    const offCtx = offCanvas.getContext('2d');
    offCtx.drawImage(img, 0, 0, canvas.width, canvas.height);
    let imageData = offCtx.getImageData(0, 0, canvas.width, canvas.height);
    
    if (document.getElementById('ditherEnable')?.checked) {
        const alg = document.getElementById('ditherAlg').value;
        const strength = parseFloat(document.getElementById('ditherStrength').value);
        const contrast = parseFloat(document.getElementById('ditherContrast').value);
        const mode = document.getElementById('ditherMode').value;
        let temp = new ImageData(new Uint8ClampedArray(imageData.data), canvas.width, canvas.height);
        temp = adjustContrast(temp, contrast);
        temp = ditherImage(temp, alg, strength, mode);
        imageData.data.set(temp.data);
    }
    ctx.putImageData(imageData, 0, 0);
    if (paintManager) paintManager.saveToHistory();
    addLog(`预览完成（尺寸：${canvas.width}x${canvas.height}）`);
}

// 合并预览 A/B 面（左右并排）
async function previewBothOnCanvas(fileA, fileB) {
    const imgA = await loadImageFromFile(fileA);
    const imgB = await loadImageFromFile(fileB);
    const halfWidth = canvas.width / 2;
    const offCanvas = document.createElement('canvas');
    offCanvas.width = canvas.width;
    offCanvas.height = canvas.height;
    const offCtx = offCanvas.getContext('2d');
    offCtx.drawImage(imgA, 0, 0, halfWidth, canvas.height);
    offCtx.drawImage(imgB, halfWidth, 0, halfWidth, canvas.height);
    let imageData = offCtx.getImageData(0, 0, canvas.width, canvas.height);
    
    if (document.getElementById('ditherEnable')?.checked) {
        const alg = document.getElementById('ditherAlg').value;
        const strength = parseFloat(document.getElementById('ditherStrength').value);
        const contrast = parseFloat(document.getElementById('ditherContrast').value);
        const mode = document.getElementById('ditherMode').value;
        let temp = new ImageData(new Uint8ClampedArray(imageData.data), canvas.width, canvas.height);
        temp = adjustContrast(temp, contrast);
        temp = ditherImage(temp, alg, strength, mode);
        imageData.data.set(temp.data);
    }
    ctx.putImageData(imageData, 0, 0);
    if (paintManager) paintManager.saveToHistory();
    addLog("合并预览完成（左A右B）");
}


/**
 * 驱动预设配置模块
 * 说明：通过选择不同的预设，动态更新 epddriver 下拉列表，
 *      并自动触发 updateDitcherOptions() 更新颜色模式/画布尺寸。
 *      方便后续添加其他驱动配置，只需在 DRIVER_PRESETS 数组中增加一项即可。
 */

// 预设驱动选项模板（HTML 字符串）
const DRIVER_PRESETS = [
    {
        id: "dongshan",
        name: "东山驱动",
        // 选项HTML（与原 QuDong_DongShan 完全一致）
        optionsHtml: `
                    <option value="1d" data-color="blackWhiteColor" data-size="1.54_152_152">1.54寸 (黑白低分, UC8176)</option>
                    <option value="22" data-color="blackWhiteColor" data-size="1.54_152_152">1.54寸OPM(黑白低分, SSD1675B)</option>
                    <option value="17" data-color="threeColor" data-size="1.54_200_200">1.54寸 (三色, UC8176)</option>
                    <option value="19" data-color="blackWhiteColor" data-size="2.13_104_212">2.13寸低分(黑白, SSD1619)</option>
                    <option value="0e" data-color="blackWhiteColor" data-size="2.13_128_250">2.13寸 (黑白, SSD1619)</option>
                    <option value="0f" data-color="threeColor" data-size="2.13_128_250">2.13寸 (三色, SSD1619)</option>
                    <option value="21" data-color="blackWhiteColor" data-size="2.7_176_264">2.7寸LG(黑白, IL91874)</option>
                    <option value="13" data-color="fourColor" data-size="2.8_152_296">2.8寸 (四色, JD79668)</option>
                    <option value="11" data-color="blackWhiteColor" data-size="2.9_128_296">2.9寸 (黑白, SSD1619)</option>
                    <option value="12" data-color="threeColor" data-size="2.9_128_296">2.9寸 (三色, SSD1619)</option>
                    <option value="1b" data-color="blackWhiteColor" data-size="2.9_128_296">2.9寸 (黑白, SSD1680)</option>
                    <option value="20" data-color="blackWhiteColor" data-size="2.9_128_296">2.9寸 (黑白, UC8151D)</option>
                    <option value="10" data-color="fourColor" data-size="3.1_300_300">3.1寸 (四色, JD79665)</option>
                    <option value="27" data-color="sixColor" data-size="3.68_792_528">3.68寸 (六色, 高分E6)</option>
                    <option value="18" data-color="threeColor" data-size="3.7_416_240">3.7寸 (三色, AI智屏壳)</option>
                    <option value="1c" data-color="fourColor" data-size="3.97_800_480">3.97寸 (四色, 方角四色屏)</option>
                    <option value="14" data-color="fourColor" data-size="3.98_768_552">3.98寸 (四色, 华为手机壳A0)</option>
                    <option value="15" data-color="fourColor" data-size="3.98_768_552">3.98寸 (四色, 华为手机壳A1)</option>
                    <option value="23" data-color="fourColor" data-size="3.98_768_552">3.98寸 (四色, A1-202511)</option>
                    <option value="1f" data-color="sixColor" data-size="3.98_768_552">3.98寸 (六色, 高分E6)</option>
                    <option value="01" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 (黑白, UC8176)</option>
                    <option value="02" data-color="threeColor" data-size="4.2_400_300" selected>4.2寸 (三色, UC8176)</option>
                    <option value="16" data-color="threeColor" data-size="4.2_400_300">4.2寸 (三色, SES_4.2BWR_GL340)</option>
                    <option value="03" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 (黑白, SSD1619)</option>
                    <option value="04" data-color="threeColor" data-size="4.2_400_300">4.2寸 (三色, SSD1619)</option>
                    <option value="05" data-color="fourColor" data-size="4.2_400_300">4.2寸 (四色, JD79668)</option>
                    <option value="24" data-color="fourColor" data-size="4.37_512_368">4.37寸 (四色, JD79665-A1)</option>
                    <option value="1e" data-color="blackWhiteColor" data-size="5.83_600_448">5.83寸 (黑白, JD79583)</option>
                    <option value="0d" data-color="fourColor" data-size="5.83_648_480">5.83寸 (四色, JD79665)</option>
                    <option value="25" data-color="fourColor" data-size="7.3E6_800_480">7.3寸 (四色, JD79665-A1)</option>
                    <option value="FF" data-color="sevenColor" data-size="7.3E6_800_480">7.3寸 (七色, Spectra 6)</option>
                    <option value="2b" data-color="threeColor" data-size="7.4_800_480">7.4寸 (三色, SES7.4_GU140)</option>
                    <option value="06" data-color="blackWhiteColor" data-size="7.5_800_480">7.5寸 (黑白, UC8179)</option>
                    <option value="07" data-color="threeColor" data-size="7.5_800_480">7.5寸 (三色, UC8179)</option>
                    <option value="0c" data-color="fourColor" data-size="7.5_800_480">7.5寸 (四色, JD79665)</option>
                    <option value="08" data-color="blackWhiteColor" data-size="7.5_640_384">7.5寸低分 (黑白, UC8159)</option>
                    <option value="09" data-color="threeColor" data-size="7.5_640_384">7.5寸低分 (三色, UC8159)</option>
                    <option value="0a" data-color="blackWhiteColor" data-size="7.5_880_528">7.5寸HD (黑白, SSD1677)</option>
                    <option value="0b" data-color="threeColor" data-size="7.5_880_528">7.5寸HD (三色, SSD1677)</option>
                    <option value="26" data-color="fourColor" data-size="9.7_960_680">9.7寸 (四色, CSOT970)</option>
        `
    },
    {
        id: "GuoWangYanYu",
        name: "過往煙雨",
        optionsHtml: `
						<option value="01" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 (黑白, UC8176)</option>
						<option value="03" data-color="threeColor" data-size="4.2_400_300">4.2寸 (三色, UC8176)</option>
						<option value="04" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 (黑白, SSD1619)</option>
						<option value="02" data-color="threeColor" data-size="4.2_400_300">4.2寸 (三色, SSD1619)</option>
						<option value="05" data-color="fourColor" data-size="4.2_400_300">4.2寸 (四色, JD79668)</option>
						<option value="0d" data-color="fourColor" data-size="3.7_416_240">3.7BWRY (四色, GDEM037F51)</option>
						<option value="0e" data-color="threeColor" data-size="3.7_416_240">3.7BWR (三色, GDEY037Z03)</option>
						<option value="0f" data-color="threeColor" data-size="3.7_416_240">3.7BWR (三色, YS4370JS0C3)</option>
						<option value="12" data-color="threeColor" data-size="3.7_416_240">3.7BWR(三色，LG 3.7寸）</option>
						<option value="10" data-color="fourColor" data-size="3.98_768_552">3.98寸（四色，SE0398NZ07A0）</option>
						<option value="11" data-color="fourColor" data-size="3.98_768_552">3.98寸（四色，SE0398NZ07A1）</option>
						<option value="13" data-color="fourColor" data-size="3.98_768_552" selected>3.98寸（四色，SE0398NZ07-New-A1）</option>
						<option value="14" data-color="fourColor" data-size="3.87_800_552">3.87寸（四色，KEGM038701E01-J665）</option>
						<option value="15" data-color="fourColor" data-size="9.7_960_680">9.7寸（四色，GDEY133F91）</option>
						<option value="06" data-color="blackWhiteColor" data-size="7.5_800_480">7.5寸 (黑白, UC8179)</option>
						<option value="07" data-color="threeColor" data-size="7.5_800_480">7.5寸 (三色, UC8179)</option>
						<option value="0c" data-color="fourColor" data-size="7.5_800_480">7.5寸 (四色, JD79668)</option>
						<option value="08" data-color="blackWhiteColor" data-size="7.5_640_384">7.5寸低分 (黑白, UC8159)</option>
						<option value="09" data-color="threeColor" data-size="7.5_640_384">7.5寸低分 (三色, UC8159)</option>
						<option value="0a" data-color="blackWhiteColor" data-size="7.5_880_528">7.5寸HD (黑白, SSD1677)</option>
						<option value="0b" data-color="threeColor" data-size="7.5_880_528">7.5寸HD (三色, SSD1677)</option>
        `
    }, 
    {
        id: "tsl0922",
        name: "TSL0922驱动",
        // 选项HTML（与原 QuDong_Tsl0922 完全一致）
        optionsHtml: `
                    <!-- ====== 大屏 (ws) ====== -->
                    <option value="13" data-color="fourColor" data-size="3.98_768_552">3.98寸A0 (四色, JD79665)</option>
                    <option value="14" data-color="fourColor" data-size="3.98_768_552">3.98寸A1 (四色, JD79665)</option>
                    <option value="01" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 (黑白, UC8176)</option>
                    <option value="03" data-color="threeColor" data-size="4.2_400_300">4.2寸 (三色, UC8176)</option>
                    <option value="04" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 (黑白, SSD1619)</option>
                    <option value="02" data-color="threeColor" data-size="4.2_400_300">4.2寸 (三色, SSD1619)</option>
                    <option value="17" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 (黑白, SSD1683)</option>
                    <option value="16" data-color="threeColor" data-size="4.2_400_300">4.2寸 (三色, SSD1683)</option>
                    <option value="05" data-color="fourColor" data-size="4.2_400_300">4.2寸 (四色, JD79668)</option>
                    <option value="28" data-color="blackWhiteColor" data-size="5.81_720_256">5.81寸 (黑白, 龙亭)</option>
                    <option value="29" data-color="threeColor" data-size="5.81_720_256">5.81寸 (三色, 龙亭)</option>
                    <option value="19" data-color="blackWhiteColor" data-size="5.83_648_480">5.83寸 (黑白, UC8179)</option>
                    <option value="18" data-color="threeColor" data-size="5.83_648_480">5.83寸 (三色, UC8179)</option>
                    <option value="0f" data-color="blackWhiteColor" data-size="5.83_648_480">5.83寸 (黑白, JD79686)</option>
                    <option value="0e" data-color="threeColor" data-size="5.83_648_480">5.83寸 (三色, JD79686)</option>
                    <option value="0d" data-color="fourColor" data-size="5.83_648_480">5.83寸 (四色, JD79665)</option>
                    <option value="2a" data-color="blackWhiteColor" data-size="7.4_800_480">7.4寸 (黑白, 龙亭)</option>
                    <option value="2b" data-color="threeColor" data-size="7.4_800_480">7.4寸 (三色, 龙亭)</option>
                    <option value="06" data-color="blackWhiteColor" data-size="7.5_800_480">7.5寸 (黑白, UC8179)</option>
                    <option value="07" data-color="threeColor" data-size="7.5_800_480">7.5寸 (三色, UC8179)</option>
                    <option value="0c" data-color="fourColor" data-size="7.5_800_480">7.5寸 (四色, JD79665)</option>
                    <option value="08" data-color="blackWhiteColor" data-size="7.5_640_384">7.5寸低分 (黑白, UC8159)</option>
                    <option value="09" data-color="threeColor" data-size="7.5_640_384">7.5寸低分 (三色, UC8159)</option>
                    <option value="0a" data-color="blackWhiteColor" data-size="7.5_880_528">7.5寸HD (黑白, SSD1677)</option>
                    <option value="0b" data-color="threeColor" data-size="7.5_880_528">7.5寸HD (三色, SSD1677)</option>
                    <option value="1a" data-color="fourColor" data-size="9.7_960_672">9.7寸 (四色, SSD2677)</option>
                    <option value="1b" data-color="fourColor" data-size="9.7_960_672">9.7寸 (四色, SSD2677, LUT)</option>
                    <option value="11" data-color="threeColor" data-size="10.2_960_640">10.2寸 (三色, SSD1677)</option>
                    <option value="12" data-color="blackWhiteColor" data-size="10.2_960_640">10.2寸 (黑白, SSD1677)</option>
                    <option value="10" data-color="fourColor" data-size="10.2_960_640">10.2寸 (四色, SSD2677)</option>
                    <option value="1c" data-color="fourColor" data-size="10.2_960_640">10.2寸 (四色, SSD2677, LUT)</option>
                    <option value="15" data-color="sixColor" data-size="7.3E6_800_480">7.3寸 (六色, Spectra 6)</option>
                    
                    <!-- ====== 小屏 (ps) ====== -->
                    <option value="33" data-color="blackWhiteColor" data-size="2.13_250_122">2.13寸 (黑白, SSD1675)</option>
                    <option value="32" data-color="threeColor" data-size="2.13_250_122">2.13寸 (三色, SSD1675)</option>
                    <option value="35" data-color="blackWhiteColor" data-size="2.13_212_104">2.13寸低分 (黑白, SSD1675)</option>
                    <option value="34" data-color="threeColor" data-size="2.13_212_104">2.13寸低分 (三色, SSD1675)</option>
                    <option value="3b" data-color="blackWhiteColor" data-size="2.13_250_122">2.13寸 (黑白, SSD1680)</option>
                    <option value="3a" data-color="threeColor" data-size="2.13_250_122">2.13寸 (三色, SSD1680)</option>
                    <option value="4e" data-color="threeColor" data-size="2.13_250_122">2.13寸 (三色, SSD1680, ZK)</option>
                    <option value="48" data-color="blackWhiteColor" data-size="2.13_212_104">2.13寸低分 (黑白, SSD1680)</option>
                    <option value="47" data-color="threeColor" data-size="2.13_212_104">2.13寸低分 (三色, SSD1680)</option>
                    <option value="4d" data-color="blackWhiteColor" data-size="2.13_250_122">2.13寸 (黑白, UC8151)</option>
                    <option value="37" data-color="blackWhiteColor" data-size="2.13_250_122">2.13寸 (黑白, UC8151)</option>
                    <option value="36" data-color="threeColor" data-size="2.13_250_122">2.13寸 (三色, UC8151)</option>
                    <option value="39" data-color="blackWhiteColor" data-size="2.13_212_104">2.13寸低分 (黑白, UC8151)</option>
                    <option value="38" data-color="threeColor" data-size="2.13_212_104">2.13寸低分 (三色, UC8151)</option>
                    <option value="4c" data-color="blackWhiteColor" data-size="2.13_250_122">2.13寸 (黑白, JD79651)</option>
                    <option value="4b" data-color="threeColor" data-size="2.13_250_122">2.13寸 (三色, JD79651)</option>
                    <option value="4a" data-color="blackWhiteColor" data-size="2.66_296_152">2.6寸 (黑白, SSD1675)</option>
                    <option value="49" data-color="threeColor" data-size="2.66_296_152">2.6寸 (三色, SSD1675)</option>
                    <option value="3d" data-color="blackWhiteColor" data-size="2.66_296_152">2.6寸 (黑白, SSD1680)</option>
                    <option value="3c" data-color="threeColor" data-size="2.66_296_152">2.6寸 (三色, SSD1680)</option>
                    <option value="3f" data-color="blackWhiteColor" data-size="2.66_296_152">2.6寸 (黑白, UC8151)</option>
                    <option value="3e" data-color="threeColor" data-size="2.66_296_152">2.6寸 (三色, UC8151)</option>
                    <option value="45" data-color="blackWhiteColor" data-size="2.9_296_128">2.9寸 (黑白, SSD1675)</option>
                    <option value="44" data-color="threeColor" data-size="2.9_296_128">2.9寸 (三色, SSD1675)</option>
                    <option value="41" data-color="blackWhiteColor" data-size="2.9_296_128">2.9寸 (黑白, SSD1680)</option>
                    <option value="40" data-color="threeColor" data-size="2.9_296_128">2.9寸 (三色, SSD1680)</option>
                    <option value="43" data-color="blackWhiteColor" data-size="2.9_296_128">2.9寸 (黑白, UC8151)</option>
                    <option value="42" data-color="threeColor" data-size="2.9_296_128">2.9寸 (三色, UC8151)</option>
                    <option value="46" data-color="blackWhiteColor" data-size="2.9_296_128">2.9寸 (黑白, SSD1608)</option>
        `
    }, 
    // 👇 后续如需添加其他驱动预设，只需在此继续增加对象即可
    {
        id: "260OnlyOne",
        name: "2.66寸52810专用",
        optionsHtml: `
                    <option value="01" data-color="threeColor" data-size="2.66_152_296" selected>2.66寸 (三色, SSD1680)</option>
        `
    }, 
    {
        id: "breeze4dev",
        name: "breeze4dev驱动",
        optionsHtml: `
						<option value="01" data-color="blackWhiteColor" data-size="4.2_400_300">4.2寸 黑白 (UC8176)</option>
						<option value="02" data-color="threeColor" data-size="4.2_400_300">4.2寸 BWR (SSD1619)</option>
						<option value="03" data-color="threeColor" data-size="4.2_400_300">4.2寸 BWR (UC8176)</option>
						<option value="06" data-color="threeColor" data-size="2.13_250_122">2.13寸 三色 (SSD16xx)</option>
						<option value="08" data-color="threeColor" data-size="2.13_250_122" selected>2.13寸 三色 CE (SSD16xx)</option>
						<option value="07" data-color="threeColor" data-size="2.9_296_128">2.9寸 三色 (SSD16xx)</option>
						<option value="09" data-color="threeColor" data-size="2.9_296_128">2.9寸 三色 CE (SSD16xx)</option>
						<option value="0a" data-color="blackWhiteColor" data-size="2.13_212_104">2.13寸 黑白 (SSD16xx)</option>
						<option value="0b" data-color="blackWhiteColor" data-size="2.13_212_104">2.13寸 黑白 CE (SSD16xx)</option>
        `
    }
];

/**
 * 根据预设ID更新 epddriver 的下拉选项
 * @param {string} presetId 预设ID（对应 DRIVER_PRESETS 中的 id）
 */
function applyDriverPreset(presetId) {
    const preset = DRIVER_PRESETS.find(p => p.id === presetId);
    if (!preset) return;
    const epddriver = document.getElementById("epddriver");
    if (!epddriver) return;
    // 使用 innerHTML 动态生成驱动选项（保留原有方式）
    epddriver.innerHTML = preset.optionsHtml;
    // 触发 updateDitcherOptions() 同步颜色模式、画布尺寸等
    if (typeof updateDitcherOptions === 'function') {
        updateDitcherOptions();
    }
    // 可选：手动派发 change 事件以保证外部监听
    epddriver.dispatchEvent(new Event('change'));
}

function applyDriverPresetAll(presetId) {
    const container = document.getElementById("driverPreset");
    if (!container) return;
    const preset = DRIVER_PRESETS.find(p => p.id === presetId);
    if (!preset) return;
    const epddriver = document.getElementById("epddriver");
    if (!epddriver) return;
    container.value = presetId;
    // 替换选项
    epddriver.innerHTML = preset.optionsHtml;

    // 如果已保存设备驱动值，尝试选中该值
    if (deviceDriverValue) {
        let found = false;
        for (let i = 0; i < epddriver.options.length; i++) {
            if (epddriver.options[i].value === deviceDriverValue) {
                epddriver.value = deviceDriverValue;
                found = true;
                break;
            }
        }
        if (!found) {
            // 如果设备驱动值不在预设中，保留预设的默认选中（即不做额外操作）
            // 但需要确保有一个选项被选中（可能预设中已有 selected）
        }
    }
    // 调用 updateDitcherOptions（现在有容错）
    if (typeof updateDitcherOptions === 'function') {
        updateDitcherOptions();
    }
    epddriver.dispatchEvent(new Event('change'));
}

// 初始化驱动预设下拉选择器
function initDriverPresetSelector() {
    const container = document.getElementById("driverPreset");
    if (!container) return;
    // 构建选项
    DRIVER_PRESETS.forEach(preset => {
        const option = document.createElement("option");
        option.value = preset.id;
        option.textContent = preset.name;
        container.appendChild(option);
    });
    // 默认选中“东山驱动”
    container.value = 'dongshan';
    // 监听变化
    container.addEventListener("change", (e) => {
        applyDriverPreset(e.target.value);
    });
    // 立即应用默认预设
    applyDriverPreset('dongshan');
}


// ==================== 主入口 ====================
document.body.onload = () => {
    textDecoder = null;
    canvas = document.getElementById('canvas');
    ctx = canvas.getContext("2d", { willReadFrequently: true });
    ctx.fillStyle = 'white';
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    paintManager = new PaintManager(canvas, ctx);
    cropManager = new CropManager(canvas, ctx, paintManager);
    paintManager.initPaintTools();
    cropManager.initCropTools();

    initEventHandlers();
    updateButtonStatus();
    checkDebugMode();

    const initEditors = () => {
        initImageEditor();
        initScheduleEditor();
        initTodoEditor();
        initCardEditor();
        initWifiEditor();
    };
    if (typeof requestIdleCallback === 'function') {
        requestIdleCallback(initEditors, { timeout: 200 });
    } else {
        setTimeout(initEditors, 0);
    }
};

// 事件初始化（包含新增亮度滑块和同步时间按钮的监听）
function initEventHandlers() {
    document.getElementById("ditherStrength").addEventListener("input", (e) => {
        document.getElementById("ditherStrengthValue").innerText = parseFloat(e.target.value).toFixed(1);
        applyDither();
    });
    document.getElementById("ditherContrast").addEventListener("input", (e) => {
        document.getElementById("ditherContrastValue").innerText = parseFloat(e.target.value).toFixed(1);
        applyDither();
    });
    // 新增亮度滑块
    const brightnessSlider = document.getElementById('ditherBrightness');
    const brightnessValue = document.getElementById('ditherBrightnessValue');
    if (brightnessSlider && brightnessValue) {
        brightnessSlider.addEventListener('input', (e) => {
            ditherBrightness = parseFloat(e.target.value);
            brightnessValue.innerText = ditherBrightness.toFixed(1);
            applyDither();
        });
    }
    const importBtn = document.getElementById("importholidaybutton");
    const holidayFile = document.getElementById("holidayJsonFile");
    if (importBtn && holidayFile) {
        importBtn.addEventListener('click', () => holidayFile.click());
        holidayFile.addEventListener('change', (e) => {
            const file = e.target.files[0];
            if (file) {
                importHolidayJsonFile(file);
                holidayFile.value = '';
            }
        });
    }
    // 新增“同步时间”按钮监听
    const syncTimeBtn = document.getElementById("syncTimeOnlyBtn");
    if (syncTimeBtn) {
        syncTimeBtn.addEventListener('click', () => syncTimeOnly());
    }
    //新增"下载图片"按钮监听
    const downloadImgBtn = document.getElementById('download-image-btn');
    if (downloadImgBtn) {
        downloadImgBtn.addEventListener('click', downloadImage);
    }
    
    // ---------- A/B面预览功能 ----------
    const previewABtn = document.getElementById('previewA');
    const previewBBtn = document.getElementById('previewB');
    const syncBothBtn = document.getElementById('syncBothToCanvas');

    if (previewABtn) {
        previewABtn.addEventListener('click', async () => {
            const file = document.getElementById('imageFileA')?.files[0];
            if (!file) { addLog("请先选择A面图片"); return; }
            await previewImageOnCanvas(file);
        });
    }
    if (previewBBtn) {
        previewBBtn.addEventListener('click', async () => {
            const file = document.getElementById('imageFileB')?.files[0];
            if (!file) { addLog("请先选择B面图片"); return; }
            await previewImageOnCanvas(file);
        });
    }
    if (syncBothBtn) {
        syncBothBtn.addEventListener('click', async () => {
            const fileA = document.getElementById('imageFileA')?.files[0];
            const fileB = document.getElementById('imageFileB')?.files[0];
            if (!fileA || !fileB) { addLog("请同时选择A面和B面图片"); return; }
            await previewBothOnCanvas(fileA, fileB);
        });
    }
    initDriverPresetSelector();//初始化驱动预设配置模块
    document.addEventListener('visibilitychange', () => {
        if (!document.hidden) {
            // 重新检查协议UI，强制重绘工具栏
            updateUIBasedOnProtocol();
            // 若当前有画板，重绘一次确保光标等正常
            //if (paintManager) paintManager.redrawAll();
        }
    });
    // 在 initEventHandlers 末尾添加
    const syncABtn = document.getElementById('syncToABtn');
    const syncBBtn = document.getElementById('syncToBBtn');
    if (syncABtn) syncABtn.addEventListener('click', () => syncCurrentCanvasToSide('A'));
    if (syncBBtn) syncBBtn.addEventListener('click', () => syncCurrentCanvasToSide('B'));
}

function checkDebugMode() {
    const link = document.getElementById('debug-toggle');
    const debug = new URLSearchParams(window.location.search).get('debug') === 'true';
    if (debug) {
        document.body.classList.add('dark-mode');
        if (link) {
            link.innerHTML = '正常模式';
            link.setAttribute('href', window.location.pathname);
        }
        addLog("注意：开发模式功能已开启！不懂请不要随意修改，否则后果自负！");
    } else {
        document.body.classList.remove('dark-mode');
        if (link) {
            link.innerHTML = '开发模式';
            link.setAttribute('href', window.location.pathname + '?debug=true');
        }
    }
}
