/**
 * ═══════════════════════════════════════════════════════════════
 * BTC/USD PRO v3.3 — Multi-Indicator AI Intelligence & Profit Engine
 * Real-Time Binance WebSocket + Multi-Timeframe Analysis + Kelly Edge
 * ═══════════════════════════════════════════════════════════════
 *
 * CORE UPGRADES & PROFIT ARCHITECTURE:
 * 1. Mathematical Accuracy:
 *    - Robust NaN-tolerant SMA & EMA (eliminating NaN poisoning in MACD & StochRSI).
 *    - Real MACD Signal & Histogram calculation (fixed 0-signal bug).
 *    - Accurate StochRSI %K & %D smoothing (fixed 50-stuck %D).
 *    - Corrected Regular & Hidden Divergence formulas (fixed inverted labels).
 * 2. Profit & Risk Opportunity Engine:
 *    - 3-Tier Take Profit Ladder (TP1: 1.5R partial scalp, TP2: 2.8R swing, TP3: 4.5R trend runner).
 *    - Structural S/R & Volume Profile Point of Control (POC) detection.
 *    - Mathematical Expectancy ($EV) computation per trade.
 *    - Kelly Criterion & Volatility-capped Position Sizing.
 *    - Trailing Stop & Break-Even execution playbook.
 * 3. Multi-Timeframe Engine with TTL Cache:
 *    - Fixed 1h omission bug when switching timeframes.
 *    - In-memory candle caching with TTL to prevent Binance 429 rate-limiting.
 * 4. Custom Chart with Volume & Key Levels:
 *    - Live volume histogram bars (color-coded).
 *    - Entry, Stop Loss, TP1, TP2, TP3, and POC guidelines with price labels.
 * 5. Reliability:
 *    - 15s WebSocket silence watchdog + exponential backoff with jitter.
 *    - Backward-compatible test hooks for data quality tests.
 */

'use strict';

// ══════════════════════════════════════════════════════
// 1. CONSTANTS & CONFIGURATION
// ══════════════════════════════════════════════════════

const CONFIG = {
  MAX_CANDLES: 250,
  MIN_CANDLES: 30,
  RECONNECT_BASE_DELAY: 1000,
  RECONNECT_MAX_DELAY: 30000,
  RECONNECT_JITTER: 0.3,
  PRICE_FLASH_DURATION: 350,
  RENDER_THROTTLE_MS: 80,
  FALLBACK_POLL_INTERVAL: 3000,
  API_TIMEOUT: 8000,
  WEBSOCKET_URL: 'wss://stream.binance.com:9443/stream',
  REST_BASE: 'https://api.binance.com/api/v3',
  DATA_AGE_LIMITS: {
    '15m': 1000 * 60 * 20,
    '1h': 1000 * 60 * 90,
    '4h': 1000 * 60 * 180,
    '1d': 1000 * 60 * 60 * 24 * 2,
  },
  // Cache TTL for multi-timeframe REST requests (avoids spamming API)
  TF_CACHE_TTL: {
    '15m': 45000,
    '1h': 120000,
    '4h': 300000,
    '1d': 600000,
  },
  // Binance taker fee rate (both per side) — used to compute NET expectancy.
  FEE_RATE: 0.001, // 0.1% round-trip assumption (maker+taker paired)
};

const INDICATOR_WEIGHTS = {
  '15m': { ema: 15, macd: 15, rsi: 12, stoch: 10, bb: 8, adx: 10, vwap: 8, volume: 10, divergence: 7, macro: 5 },
  '1h':  { ema: 20, macd: 18, rsi: 14, stoch: 10, bb: 8, adx: 10, vwap: 8, volume: 6, divergence: 4, macro: 2 },
  '4h':  { ema: 22, macd: 18, rsi: 15, stoch: 8, bb: 7, adx: 12, vwap: 6, volume: 5, divergence: 3, macro: 4 },
  '1d':  { ema: 25, macd: 15, rsi: 15, stoch: 6, bb: 6, adx: 14, vwap: 4, volume: 4, divergence: 2, macro: 9 },
};

const TF_WEIGHTS = { '15m': 0.10, '1h': 0.40, '4h': 0.30, '1d': 0.20 };

// ══════════════════════════════════════════════════════
// 2. UTILITY FUNCTIONS
// ══════════════════════════════════════════════════════

const $ = (id) => (typeof document !== 'undefined' && document.getElementById ? document.getElementById(id) : null);
const clamp = (val, min, max) => Math.min(max, Math.max(min, val));
const lerp = (a, b, t) => a + (b - a) * t;

const formatMoney = (val, decimals = 2) => {
  const num = Number(val);
  if (!Number.isFinite(num)) return '—';
  return `$${num.toLocaleString('en-US', {
    minimumFractionDigits: decimals,
    maximumFractionDigits: decimals,
  })}`;
};

const formatPercent = (val) => {
  const num = Number(val);
  if (!Number.isFinite(num)) return '0.00%';
  return `${num >= 0 ? '+' : ''}${num.toFixed(2)}%`;
};

const formatVolume = (val) => {
  const num = Number(val);
  if (!Number.isFinite(num)) return '0';
  if (num >= 1e9) return `${(num / 1e9).toFixed(2)}B`;
  if (num >= 1e6) return `${(num / 1e6).toFixed(2)}M`;
  if (num >= 1e3) return `${(num / 1e3).toFixed(1)}K`;
  return num.toFixed(0);
};

const sleep = (ms) => new Promise(resolve => setTimeout(resolve, ms));

const getLastValid = (arr, fallback = 0) => {
  if (!arr || !arr.length) return fallback;
  for (let i = arr.length - 1; i >= 0; i--) {
    const v = arr[i];
    if (typeof v === 'number' && !Number.isNaN(v) && Number.isFinite(v)) return v;
  }
  return fallback;
};

// ══════════════════════════════════════════════════════
// 3. GLOBAL STATE
// ══════════════════════════════════════════════════════

const state = {
  interval: '1h',
  tvWidget: null,
  candles: [],
  analysis: null,
  profitSetup: null,
  multiTF: {},
  chartView: 'tv',
  isFetching: false,
  dataHealth: {
    valid: false,
    status: 'unknown',
    source: 'unknown',
    ageMs: Number.POSITIVE_INFINITY,
    reason: 'No data loaded',
    freshness: 0,
    lastChecked: 0,
  },
  performance: {
    totalSignals: 0,
    wins: 0,
    losses: 0,
    avgR: 0,
    profitFactor: 1,
    maxDrawdown: 0,
    lastRun: null,
    history: [],
  },

  // Multi-timeframe cache to prevent rate-limit bans
  tfCache: {
    '15m': { candles: null, ticker: null, timestamp: 0 },
    '1h':  { candles: null, ticker: null, timestamp: 0 },
    '4h':  { candles: null, ticker: null, timestamp: 0 },
    '1d':  { candles: null, ticker: null, timestamp: 0 },
  },

  // WebSocket
  ws: null,
  wsReconnectAttempts: 0,
  wsLastTick: Date.now(),
  wsTickCount: 0,
  wsPrevPrice: null,
  wsFlashTimer: null,
  wsReconnectTimer: null,
  wsFallbackTimer: null,
  wsWatchdogTimer: null,

  // Memoization cache for the custom SVG chart EMA lines.
  // Keyed by the last candle time + count so we only recompute
  // when the candle stack actually changes.
  chartEmaCache: {
    key: null,
    e9: null,
    e21: null,
    e50: null,
  },
  wsLatency: 0,
  wsStatus: 'disconnected',

  // Performance & batching
  renderScheduled: false,
  lastRenderTime: 0,

  // Ticker cache
  ticker: { price: 0, change: 0, changePercent: 0, high24: 0, low24: 0, volume24: 0 },

  // History
  priceHistory: [],
  signalHistory: [],
};

// ══════════════════════════════════════════════════════
// 4. DATA HEALTH & VALIDATION
// ══════════════════════════════════════════════════════

function assessMarketData({ candles = [], ticker = {}, source = 'unknown', interval = state.interval } = {}) {
  const now = Date.now();
  if (!Array.isArray(candles) || candles.length < CONFIG.MIN_CANDLES) {
    const summary = {
      valid: false,
      status: 'empty',
      source,
      ageMs: Number.POSITIVE_INFINITY,
      reason: 'Not enough candles for analysis',
      freshness: 0,
      lastChecked: now,
    };
    state.dataHealth = summary;
    return summary;
  }

  const lastCandle = candles[candles.length - 1];
  const ageMs = Math.max(0, now - (lastCandle.time || now));
  const limit = CONFIG.DATA_AGE_LIMITS[interval] || CONFIG.DATA_AGE_LIMITS['1h'];
  const freshness = clamp(100 - (ageMs / limit) * 100, 0, 100);

  let status = 'good';
  let valid = true;
  let reason = 'Fresh data available';

  if (ageMs > limit * 1.5) {
    status = 'stale';
    valid = false;
    reason = `Data is stale by ${Math.round(ageMs / 1000)}s`;
  } else if (ageMs > limit) {
    status = 'warning';
    valid = false;
    reason = `Data is approaching stale threshold`;
  }

  const price = Number(ticker.price || lastCandle.close || 0);
  if (!Number.isFinite(price) || price <= 0) {
    status = 'warning';
    valid = false;
    reason = 'Ticker price is invalid';
  }

  const summary = {
    valid,
    status,
    source,
    ageMs,
    reason,
    freshness: Number.isFinite(freshness) ? freshness : 0,
    lastChecked: now,
  };

  state.dataHealth = summary;
  return summary;
}

function getDataHealthSummary() {
  if (state.dataHealth && state.dataHealth.lastChecked) return state.dataHealth;
  return assessMarketData({ candles: state.candles, ticker: state.ticker, source: 'unknown', interval: state.interval });
}

// ══════════════════════════════════════════════════════
// 5. MATHEMATICAL INDICATOR FUNCTIONS (Robust & Accurate)
// ══════════════════════════════════════════════════════

/**
 * NaN-tolerant SMA calculation using sliding window.
 */
function calcSMA(values, period) {
  const n = values.length;
  const result = new Float64Array(n);
  result.fill(NaN);
  if (n < period) return result;

  // Sliding window with NaN gaps — reset window on invalid values,
  // then properly slide the start index so the window always holds exactly
  // `period` consecutive valid values.
  let sum = 0;
  let count = 0;
  let windowStart = -1;

  for (let i = 0; i < n; i++) {
    const v = values[i];
    if (v === null || typeof v !== 'number' || Number.isNaN(v)) {
      sum = 0;
      count = 0;
      windowStart = -1;
      continue;
    }
    if (count === 0) windowStart = i;
    sum += v;
    count++;

    if (count > period) {
      sum -= values[windowStart];
      windowStart++;
      count--;
    }
    if (count === period) {
      result[i] = sum / period;
    }
  }
  return result;
}

/**
 * NaN-tolerant EMA calculation.
 * Finds the first sequence of 'period' non-NaN values to seed the initial SMA,
 * then properly applies the multiplier without index lookahead bugs.
 */
function calcEMA(values, period) {
  const n = values.length;
  const result = new Float64Array(n);
  result.fill(NaN);
  if (n < period) return result;

  const k = 2 / (period + 1);
  let prev = NaN;
  let validCount = 0;
  let seedSum = 0;

  for (let i = 0; i < n; i++) {
    const v = values[i];
    if (v === null || typeof v !== 'number' || Number.isNaN(v)) {
      validCount = 0;
      seedSum = 0;
      prev = NaN;
      continue;
    }

    validCount++;
    seedSum += v;

    if (validCount === period) {
      prev = seedSum / period;
      result[i] = prev;
    } else if (validCount > period) {
      prev = (v - prev) * k + prev;
      result[i] = prev;
    }
  }
  return result;
}

/**
 * Wilder's smoothed Relative Strength Index (RSI).
 * Handles zero price movement cleanly (returns 50 instead of 100).
 */
function calcRSI(values, period = 14) {
  const result = new Float64Array(values.length);
  result.fill(NaN);
  if (values.length <= period) return result;

  let gains = 0, losses = 0;
  for (let i = 1; i <= period; i++) {
    const ch = values[i] - values[i - 1];
    if (ch > 0) gains += ch;
    else losses -= ch;
  }

  let avgG = gains / period;
  let avgL = losses / period;
  result[period] = (avgG + avgL === 0) ? 50 : (avgL === 0 ? 100 : 100 - (100 / (1 + avgG / avgL)));

  for (let i = period + 1; i < values.length; i++) {
    const ch = values[i] - values[i - 1];
    avgG = (avgG * (period - 1) + (ch > 0 ? ch : 0)) / period;
    avgL = (avgL * (period - 1) + (ch < 0 ? -ch : 0)) / period;
    result[i] = (avgG + avgL === 0) ? 50 : (avgL === 0 ? 100 : 100 - (100 / (1 + avgG / avgL)));
  }
  return result;
}

/**
 * MACD (12, 26, 9)
 * Correctly computes Fast, Slow, MACD Line, Signal Line (EMA 9 of MACD), and Histogram.
 */
function calcMACD(values) {
  const fast = calcEMA(values, 12);
  const slow = calcEMA(values, 26);
  const macd = new Float64Array(values.length);
  macd.fill(NaN);

  for (let i = 0; i < values.length; i++) {
    macd[i] = (!Number.isNaN(fast[i]) && !Number.isNaN(slow[i])) ? fast[i] - slow[i] : NaN;
  }

  const signal = calcEMA(macd, 9);
  const hist = new Float64Array(values.length);
  hist.fill(NaN);

  for (let i = 0; i < values.length; i++) {
    hist[i] = (!Number.isNaN(macd[i]) && !Number.isNaN(signal[i])) ? macd[i] - signal[i] : NaN;
  }

  return { macd, signal, hist };
}

/**
 * Bollinger Bands (20, 2)
 */
function calcBB(values, period = 20, mult = 2) {
  const mid = calcSMA(values, period);
  const upper = new Float64Array(values.length);
  const lower = new Float64Array(values.length);
  const pctB = new Float64Array(values.length);
  const bandwidth = new Float64Array(values.length);
  upper.fill(NaN);
  lower.fill(NaN);
  pctB.fill(NaN);
  bandwidth.fill(NaN);

  for (let i = period - 1; i < values.length; i++) {
    if (Number.isNaN(mid[i])) continue;
    let sumSq = 0;
    for (let j = i - period + 1; j <= i; j++) {
      sumSq += (values[j] - mid[i]) ** 2;
    }
    const std = Math.sqrt(sumSq / period);
    upper[i] = mid[i] + mult * std;
    lower[i] = mid[i] - mult * std;
    const bandSpan = upper[i] - lower[i];
    pctB[i] = bandSpan === 0 ? 50 : ((values[i] - lower[i]) / bandSpan) * 100;
    bandwidth[i] = mid[i] === 0 ? 0 : (bandSpan / mid[i]) * 100;
  }

  return { upper, middle: mid, lower, pctB, bandwidth };
}

/**
 * Average True Range (ATR)
 */
function calcATR(candles, period = 14) {
  if (candles.length < 2) return 0;
  const tr = new Float64Array(candles.length);
  tr[0] = candles[0].high - candles[0].low;

  for (let i = 1; i < candles.length; i++) {
    tr[i] = Math.max(
      candles[i].high - candles[i].low,
      Math.abs(candles[i].high - candles[i - 1].close),
      Math.abs(candles[i].low - candles[i - 1].close)
    );
  }

  const atrSeries = calcSMA(tr, period);
  return getLastValid(atrSeries, candles[candles.length - 1].close * 0.012);
}

/**
 * Average Directional Index (ADX) & Directional Movement (+DI / -DI)
 */
function calcADX(candles, period = 14) {
  const n = candles.length;
  if (n <= period * 2) return { adx: 25, plusDI: 20, minusDI: 20 };

  const plusDM = new Float64Array(n);
  const minusDM = new Float64Array(n);
  const tr = new Float64Array(n);

  tr[0] = candles[0].high - candles[0].low;

  for (let i = 1; i < n; i++) {
    const hd = candles[i].high - candles[i - 1].high;
    const ld = candles[i - 1].low - candles[i].low;
    plusDM[i] = (hd > ld && hd > 0) ? hd : 0;
    minusDM[i] = (ld > hd && ld > 0) ? ld : 0;
    tr[i] = Math.max(
      candles[i].high - candles[i].low,
      Math.abs(candles[i].high - candles[i - 1].close),
      Math.abs(candles[i].low - candles[i - 1].close)
    );
  }

  const trS = calcSMA(tr, period);
  const pdS = calcSMA(plusDM, period);
  const mdS = calcSMA(minusDM, period);

  const dx = new Float64Array(n);
  dx.fill(NaN);

  for (let i = period - 1; i < n; i++) {
    const t = trS[i] || 1;
    const pDI = (pdS[i] / t) * 100;
    const mDI = (mdS[i] / t) * 100;
    const sum = pDI + mDI;
    dx[i] = sum === 0 ? 0 : (Math.abs(pDI - mDI) / sum) * 100;
  }

  const adxSeries = calcSMA(dx, period);
  const lastIdx = n - 1;
  const lastTR = trS[lastIdx] || 1;

  return {
    adx: getLastValid(adxSeries, 25),
    plusDI: (pdS[lastIdx] / lastTR) * 100,
    minusDI: (mdS[lastIdx] / lastTR) * 100,
  };
}

/**
 * Volume Weighted Average Price (VWAP)
 */
function calcVWAP(candles) {
  let pv = 0, vol = 0;
  for (const c of candles) {
    const tp = (c.high + c.low + c.close) / 3;
    pv += tp * c.volume;
    vol += c.volume;
  }
  return vol > 0 ? pv / vol : candles[candles.length - 1].close;
}

/**
 * StochRSI — Returns smoothed %K and %D
 * Accurately handles leading NaNs so %D is not stuck at 50.
 */
function calcStochRSI(values, rsiPeriod = 14, stochPeriod = 14, kSmooth = 3, dSmooth = 3) {
  const rsiV = calcRSI(values, rsiPeriod);
  const rawK = new Float64Array(values.length);
  rawK.fill(NaN);

  for (let i = rsiPeriod + stochPeriod - 1; i < values.length; i++) {
    const validSlice = [];
    for (let j = i - stochPeriod + 1; j <= i; j++) {
      if (!Number.isNaN(rsiV[j])) validSlice.push(rsiV[j]);
    }
    if (validSlice.length < stochPeriod) continue;
    const minR = Math.min(...validSlice);
    const maxR = Math.max(...validSlice);
    rawK[i] = (maxR === minR) ? 50 : ((rsiV[i] - minR) / (maxR - minR)) * 100;
  }

  const kSeries = calcSMA(rawK, kSmooth);
  const dSeries = calcSMA(kSeries, dSmooth);

  return {
    k: getLastValid(kSeries, 50),
    d: getLastValid(dSeries, 50),
    kSeries,
    dSeries,
  };
}

/**
 * Multi-Indicator Divergence Detection (RSI & MACD)
 * Corrects regular & hidden divergence classifications.
 */
function detectDivergence(candles, rsiValues, macdHistValues) {
  const n = candles.length;
  if (n < 30) return { type: 'none', strength: 0, reason: 'Insufficient bars' };

  const lookback = Math.min(28, Math.floor(n / 2));
  const prices = candles.map(c => c.close);
  const rsiArr = Array.from(rsiValues);
  const histArr = macdHistValues ? Array.from(macdHistValues) : null;

  const peaks = [];
  const troughs = [];

  for (let i = 2; i < lookback - 2; i++) {
    const idx = n - lookback + i;
    if (idx < 2 || idx >= n - 2) continue;

    // Peak
    if (prices[idx] > prices[idx - 1] && prices[idx] > prices[idx - 2] &&
        prices[idx] >= prices[idx + 1] && prices[idx] > prices[idx + 2]) {
      peaks.push({ idx, price: prices[idx], rsi: rsiArr[idx], hist: histArr ? histArr[idx] : 0 });
    }
    // Trough
    if (prices[idx] < prices[idx - 1] && prices[idx] < prices[idx - 2] &&
        prices[idx] <= prices[idx + 1] && prices[idx] < prices[idx + 2]) {
      troughs.push({ idx, price: prices[idx], rsi: rsiArr[idx], hist: histArr ? histArr[idx] : 0 });
    }
  }

  const lastPeakIdx = peaks.length >= 2 ? peaks[peaks.length - 1].idx : -1;
  const lastTroughIdx = troughs.length >= 2 ? troughs[troughs.length - 1].idx : -1;

  const checkBullish = () => {
    if (troughs.length >= 2) {
      const [t1, t2] = troughs.slice(-2);
      if (t2.price < t1.price && t2.rsi > t1.rsi) {
        const strength = clamp(Math.round((t2.rsi / (t1.rsi || 1) - 1) * 250), 30, 95);
        return { type: 'bullish', strength, reason: 'Lower Low Price + Higher Low RSI' };
      }
      if (t2.price > t1.price && t2.rsi < t1.rsi) {
        return { type: 'hidden-bullish', strength: 65, reason: 'Higher Low Price + Lower Low RSI (Trend Continuation)' };
      }
    }
    return null;
  };

  const checkBearish = () => {
    if (peaks.length >= 2) {
      const [p1, p2] = peaks.slice(-2);
      if (p2.price > p1.price && p2.rsi < p1.rsi) {
        const strength = clamp(Math.round((1 - p2.rsi / (p1.rsi || 1)) * 250), 30, 95);
        return { type: 'bearish', strength, reason: 'Higher High Price + Lower High RSI' };
      }
      if (p2.price < p1.price && p2.rsi > p1.rsi) {
        return { type: 'hidden-bearish', strength: 65, reason: 'Lower High Price + Higher High RSI (Trend Continuation)' };
      }
    }
    return null;
  };

  // Evaluate the most recent structure first to avoid stale opposing signals
  if (lastTroughIdx > lastPeakIdx) {
    const bull = checkBullish();
    if (bull) return bull;
    const bear = checkBearish();
    if (bear) return bear;
  } else {
    const bear = checkBearish();
    if (bear) return bear;
    const bull = checkBullish();
    if (bull) return bull;
  }

  return { type: 'none', strength: 0, reason: 'No divergence detected' };
}

/**
 * Volume Profile & Point of Control (POC)
 */
function calcVolumeProfile(candles, zones = 12) {
  if (!candles || candles.length < 10) return { bins: [], poc: 0 };

  const highs = candles.map(c => c.high);
  const lows = candles.map(c => c.low);
  const minP = Math.min(...lows);
  const maxP = Math.max(...highs);
  const range = maxP - minP || 1;
  const binSize = range / zones;

  const bins = new Array(zones).fill(0);

  for (const c of candles) {
    const mid = (c.high + c.low) / 2;
    const binIdx = Math.min(zones - 1, Math.max(0, Math.floor((mid - minP) / binSize)));
    bins[binIdx] += c.volume;
  }

  let maxVol = 0;
  let pocIdx = 0;
  for (let i = 0; i < zones; i++) {
    if (bins[i] > maxVol) {
      maxVol = bins[i];
      pocIdx = i;
    }
  }

  const pocPrice = minP + binSize * (pocIdx + 0.5);
  const avgVol = bins.reduce((a, b) => a + b, 0) / zones;

  const profile = bins.map((vol, i) => ({
    priceLevel: minP + binSize * (i + 0.5),
    volume: vol,
    isPoc: i === pocIdx,
    isHighVolume: vol > avgVol * 1.3,
    strength: clamp(vol / (avgVol || 1), 0, 3),
  }));

  return { bins: profile, poc: pocPrice };
}

/**
 * Structural Key Levels (Swing S/R & POC)
 */
function detectKeyLevels(candles) {
  if (!candles || candles.length < 20) {
    const p = candles && candles.length ? candles[candles.length - 1].close : 65000;
    return { support: p * 0.98, resistance: p * 1.02, poc: p, swingLows: [], swingHighs: [] };
  }

  const highs = candles.map(c => c.high);
  const lows = candles.map(c => c.low);
  const currentPrice = candles[candles.length - 1].close;

  const swingHighs = [];
  const swingLows = [];

  for (let i = 3; i < candles.length - 3; i++) {
    if (highs[i] > highs[i - 1] && highs[i] > highs[i - 2] &&
        highs[i] > highs[i + 1] && highs[i] > highs[i + 2]) {
      swingHighs.push(highs[i]);
    }
    if (lows[i] < lows[i - 1] && lows[i] < lows[i - 2] &&
        lows[i] < lows[i + 1] && lows[i] < lows[i + 2]) {
      swingLows.push(lows[i]);
    }
  }

  const supportsBelow = swingLows.filter(p => p < currentPrice);
  const resistancesAbove = swingHighs.filter(p => p > currentPrice);

  const nearestSupport = supportsBelow.length ? Math.max(...supportsBelow) : Math.min(...lows);
  const nearestResistance = resistancesAbove.length ? Math.min(...resistancesAbove) : Math.max(...highs);

  const vp = calcVolumeProfile(candles);

  return {
    support: nearestSupport,
    resistance: nearestResistance,
    poc: vp.poc || currentPrice,
    swingHighs,
    swingLows,
  };
}

// ══════════════════════════════════════════════════════
// 6. MARKET REGIME & SIGNAL CONFIRMATION
// ══════════════════════════════════════════════════════

function detectMarketRegime(candles, price, ema9, ema21, ema50, adxValue, atrValue) {
  if (!candles || candles.length < CONFIG.MIN_CANDLES) return 'unknown';

  const closes = candles.map(c => c.close);
  const recent = closes.slice(-20);
  const recentHigh = Math.max(...recent);
  const recentLow = Math.min(...recent);
  const rangePct = (recentHigh - recentLow) / (price || 1);
  const atrPct = (atrValue / (price || 1)) * 100;
  const directionBias = (ema9 > ema21 && ema21 > ema50 && price > ema21) ? 1 :
                        (ema9 < ema21 && ema21 < ema50 && price < ema21) ? -1 : 0;

  if (adxValue >= 24 && directionBias !== 0 && rangePct < 0.07) {
    return 'trending';
  }
  if (adxValue < 22 && rangePct < 0.05 && atrPct < 1.5) {
    return 'range';
  }
  if (atrPct > 2.2 || rangePct > 0.08) {
    return 'volatile';
  }
  return 'mixed';
}

function getSignalConfirmation(primaryResult) {
  if (!primaryResult) return { valid: false, confirmations: 0, reason: 'No signal data' };

  const checks = [];
  if (primaryResult.isTrending) checks.push('trend');
  // Field-safe momentum check: handle partial/fake-data objects where macd/stoch
  // may be missing (e.g. generateFallbackData or hand-built test fixtures).
  if (
    primaryResult.macd &&
    primaryResult.stoch &&
    Number.isFinite(primaryResult.macd.line) &&
    Number.isFinite(primaryResult.macd.signal) &&
    Number.isFinite(primaryResult.stoch.k) &&
    Number.isFinite(primaryResult.stoch.d) &&
    primaryResult.macd.line > primaryResult.macd.signal &&
    primaryResult.stoch.k > primaryResult.stoch.d
  ) {
    checks.push('momentum');
  }
  if (
    primaryResult.price &&
    Number.isFinite(primaryResult.ema21) &&
    Number.isFinite(primaryResult.ema9) &&
    primaryResult.price > primaryResult.ema21 &&
    primaryResult.ema9 > primaryResult.ema21
  ) {
    checks.push('structure');
  }
  if (primaryResult.volProfile && primaryResult.volProfile.bins && primaryResult.volProfile.bins.length > 0) {
    checks.push('volume');
  }

  return {
    valid: checks.length >= 2,
    confirmations: checks.length,
    reason: checks.length >= 2 ? 'Confirmed by multiple signals' : 'Not enough signal confirmation',
  };
}

function evaluateSignalThresholds(performanceSummary) {
  if (!performanceSummary) return { confidenceFloor: 60, strictMode: true };

  if (performanceSummary.winRate >= 58 && performanceSummary.profitFactor >= 1.3) {
    return { confidenceFloor: 58, strictMode: false };
  }
  if (performanceSummary.winRate >= 52 && performanceSummary.profitFactor >= 1.15) {
    return { confidenceFloor: 60, strictMode: false };
  }
  if (performanceSummary.winRate >= 45 && performanceSummary.profitFactor >= 1.0) {
    return { confidenceFloor: 68, strictMode: true };
  }
  return { confidenceFloor: 75, strictMode: true };
}

// ══════════════════════════════════════════════════════
// 7. PROFIT OPPORTUNITY & RISK MANAGEMENT ENGINE
// ══════════════════════════════════════════════════════

/**
 * Analyzes market structure, S/R, ATR, and momentum to produce:
 * - 3-Tier Take Profit (TP1 1.5R, TP2 2.8R, TP3 4.5R)
 * - Dynamic Stop Loss with structural buffer
 * - Kelly Position Sizing
 * - Mathematical Expectancy ($EV) per trade
 * - Trailing Stop Rule for locking in profit
 */
function calcProfitOpportunity(analysis, capital = 1000, riskPct = 1.5, performance) {
  if (!analysis) return null;

  const price = analysis.price;
  const isBuy = analysis.normScore >= 0;
  const atrVal = analysis.atr;
  const regime = analysis.marketRegime || 'mixed';
  const confidence = analysis.confidence || 50;
  const keyLevels = analysis.keyLevels || { support: price * 0.98, resistance: price * 1.02, poc: price };

  // Volatility and regime buffer
  const regimeMultiplier = regime === 'trending' ? 1.25 : regime === 'range' ? 1.55 : regime === 'volatile' ? 1.9 : 1.6;
  const volMultiplier = analysis.bbBandwidth > 5 ? 1.3 : 1.1;
  const baseSlDist = atrVal * regimeMultiplier * volMultiplier;

  // Align stop loss with structural support/resistance
  let slDist = baseSlDist;
  if (isBuy && keyLevels.support && keyLevels.support < price) {
    const structDist = (price - keyLevels.support) + (atrVal * 0.35);
    slDist = Math.max(baseSlDist, Math.min(baseSlDist * 1.4, structDist));
  } else if (!isBuy && keyLevels.resistance && keyLevels.resistance > price) {
    const structDist = (keyLevels.resistance - price) + (atrVal * 0.35);
    slDist = Math.max(baseSlDist, Math.min(baseSlDist * 1.4, structDist));
  }

  const stopLevel = isBuy ? Math.max(0, price - slDist) : price + slDist;

  // 3-Tier Profit Targets
  const tp1Dist = slDist * 1.5;   // Conservative Scalp / Partial Lock (1.5R)
  const tp2Dist = slDist * 2.8;   // Core Swing Target (2.8R)
  const tp3Dist = slDist * 4.5;   // Extended Trend Runner (4.5R)

  const tp1 = isBuy ? price + tp1Dist : price - tp1Dist;
  const tp2 = isBuy ? price + tp2Dist : price - tp2Dist;
  const tp3 = isBuy ? price + tp3Dist : price - tp3Dist;

  // Capital & Position Sizing
  const safeCapital = Math.max(10, Number(capital) || 1000);
  const safeRiskPct = clamp(Number(riskPct) || 1.5, 0.1, 10);
  const rawRiskUsd = (safeCapital * safeRiskPct) / 100;

  // Confidence scaling
  const confModifier = confidence >= 85 ? 1.0 : confidence >= 70 ? 0.8 : confidence >= 50 ? 0.55 : 0.3;
  const cappedRiskUsd = rawRiskUsd * confModifier;

  // Kelly Criterion fraction calculation
  // Use real tracked win-rate if we have enough signal outcomes, otherwise
  // fall back to confidence-derived estimate (backward compatible). The caller
  // may pass an explicit `performance` snapshot (e.g. for pure unit tests) —
  // otherwise we read the shared global state.
  const perf = performance || state.performance || {};
  const hasRealStats = perf.totalSignals >= 10 && perf.wins + perf.losses > 0;
  const realWinRate = hasRealStats ? (perf.wins / (perf.wins + perf.losses)) * 100 : null;
  // Blend: if real stats exist, 70% weight on reality, 30% on confidence signal.
  const effectiveWinRate = realWinRate !== null ? (realWinRate * 0.7 + confidence * 0.3) : confidence;
  const winProb = clamp(effectiveWinRate / 100, 0.35, 0.85);

  // avg RR — prefer empirically measured average R from closed trades, else 2.4R.
  let avgRR = 2.4; // composite weighted R (1.5R * 0.4 + 2.8R * 0.4 + 4.5R * 0.2 = 2.62)
  if (hasRealStats && perf.history && perf.history.length > 0) {
    const rs = perf.history.map(h => Number(h.rMultiple) || 0).filter(v => v !== 0);
    if (rs.length >= 10) {
      const realizedAvgR = rs.reduce((sum, v) => sum + v, 0) / rs.length;
      if (Number.isFinite(realizedAvgR) && realizedAvgR > 0) avgRR = clamp(realizedAvgR, 1.0, 3.5);
    }
  }

  const kellyFraction = Math.max(0.05, (winProb * avgRR - (1 - winProb)) / avgRR);
  const conservativeKellyPct = clamp(kellyFraction * 0.3, 0.05, 0.25) * safeRiskPct;
  const kellyRiskUsd = (safeCapital * conservativeKellyPct) / 100;

  // Final used risk per trade
  const usedLossUsd = Math.min(cappedRiskUsd, kellyRiskUsd, rawRiskUsd);
  const positionBtc = slDist > 0 ? usedLossUsd / slDist : 0;
  const positionUsd = positionBtc * price;

  // ── Fee-aware (NET) expectancy ──
  // Binance taker fees apply on both legs (open + close). We model a round-trip
  // fee as a fixed % of the notional (positionUsd): FEE_RATE * positionUsd.
  const feeRate = Number(CONFIG.FEE_RATE) || 0.001;
  const roundTripFeeUsd = positionUsd * feeRate;
  const feeBreakEvenR = slDist > 0 ? (roundTripFeeUsd / (positionBtc * slDist || 1)) : 0;

  // Mathematical Expectancy ($EV) — NET of fees
  // EV = (P(win) * AvgWinUSD) - (P(loss) * RiskUSD) - Fee
  const avgWinUsd = usedLossUsd * avgRR;
  const grossExpectedValueUsd = (winProb * avgWinUsd) - ((1 - winProb) * usedLossUsd);
  const expectedValueUsd = grossExpectedValueUsd - roundTripFeeUsd;
  // NET EV in R units (gross R expectancy minus fee drag in R terms).
  const expectedValueR = ((winProb * avgRR) - (1 - winProb)) - feeBreakEvenR;

  // Break-even win rate AFTER fees: f*/(f + (R multiply - f)) style.
  // At each realized target the fee drags R down, so compute net RR used for EV.
  const netRr = avgRR - feeBreakEvenR;
  const breakEvenWinRate = netRr > 0 ? (1 / (1 + netRr)) : 1;

  // Setup Classification
  let setupType = '⚡ MOMENTUM BREAKOUT';
  let trailingRule = 'เมื่อราคาถึง TP1 (1.5R): ปิดทำกำไร 40% และเลื่อน Stop Loss มาที่จุดเข้า (Break-Even) เพื่อเป็น Risk-Free Trade ทันที จากนั้นรันไม้ที่เหลือไป TP2/TP3';

  if (analysis.divergence && analysis.divergence.type !== 'none') {
    setupType = '🔄 DIVERGENCE REVERSAL';
    trailingRule = 'ตรวจพบสัญญาณ Divergence: แนะนำเข้าเทรดสั้นและขยับ Trailing Stop ตามแท่งเทียนก่อนหน้าอย่างใกล้ชิด';
  } else if (regime === 'range') {
    setupType = '📦 RANGE S/R BOUNCE';
    trailingRule = 'ตลาดไซด์เวย์: ล็อคกำไรส่วนใหญ่ที่ TP1 ทันที และห้ามถือลากข้ามกรอบแนวต้านสำคัญ';
  } else if (analysis.isTrending && Math.abs(price - analysis.ema21) < atrVal * 0.6) {
    setupType = '🛡️ EMA PULLBACK CONTINUATION';
    trailingRule = 'เข้าจังหวะย่อตัวในเทรนด์: เมื่อแตะ TP1 ให้เลื่อน SL มาบังทุน และเมื่อแตะ TP2 ให้ Trail Stop ตามแนวเส้น EMA 21';
  }

  return {
    isBuy,
    price,
    stopLevel,
    slDist,
    tp1,
    tp1Dist,
    tp2,
    tp2Dist,
    tp3,
    tp3Dist,
    rrRatio: (tp2Dist / (slDist || 1)).toFixed(1),
    usedLossUsd,
    positionBtc,
    positionUsd,
    expectedValueUsd,
    expectedValueR,
    grossExpectedValueUsd,
    roundTripFeeUsd,
    feeBreakEvenR,
    breakEvenWinRate,
    netRr,
    avgRR,
    winProb,
    setupType,
    trailingRule,
  };
}

// ══════════════════════════════════════════════════════
// 8. TIMEFRAME ANALYSIS ENGINE
// ══════════════════════════════════════════════════════

function analyzeTimeframe(candles, interval) {
  if (!candles || candles.length < CONFIG.MIN_CANDLES) return null;

  const closes = candles.map(c => c.close);
  const price = closes[closes.length - 1];
  const weights = INDICATOR_WEIGHTS[interval] || INDICATOR_WEIGHTS['1h'];

  // Core indicators
  const ema9Series = calcEMA(closes, 9);
  const ema21Series = calcEMA(closes, 21);
  const ema50Series = calcEMA(closes, 50);
  const ema200Series = calcEMA(closes, 200);

  const ema9 = getLastValid(ema9Series, price);
  const ema21 = getLastValid(ema21Series, price);
  const ema50 = getLastValid(ema50Series, price);
  // EMA200 may not have enough history (e.g. 80-candle REST fetch). Fall back
  // to the longest EMA we *do* have so the macro bias is still data-driven
  // instead of hard-coded 0.95x price.
  const ema200 = getLastValid(ema200Series, getLastValid(ema50Series, price));

  const rsiSeries = calcRSI(closes, 14);
  const rsiV = getLastValid(rsiSeries, 50);

  const stoch = calcStochRSI(closes);
  const macdData = calcMACD(closes);
  const bb = calcBB(closes);
  const adxData = calcADX(candles);
  const atrVal = calcATR(candles);
  const vwap = calcVWAP(candles);

  const macdLine = getLastValid(macdData.macd, 0);
  const macdSig = getLastValid(macdData.signal, 0);
  const macdHist = getLastValid(macdData.hist, 0);
  const macdHistPrev = macdData.hist.length > 1 ? getLastValid(macdData.hist.slice(0, -1), 0) : 0;

  const bbPctB = getLastValid(bb.pctB, 50);
  const bbBandwidth = getLastValid(bb.bandwidth, 0);
  const marketRegime = detectMarketRegime(candles, price, ema9, ema21, ema50, adxData.adx, atrVal);

  // Volume
  const volumes = candles.map(c => c.volume);
  const volSMA = calcSMA(volumes, 20);
  const avgVol = getLastValid(volSMA, 1000);
  const currVol = volumes[volumes.length - 1];
  const isHighVol = currVol > avgVol * 1.15;
  const isLowVol = currVol < avgVol * 0.6;

  // Divergence
  const divergence = detectDivergence(candles, rsiSeries, macdData.hist);

  // Volume Profile & S/R
  const volProfile = calcVolumeProfile(candles);
  const keyLevels = detectKeyLevels(candles);

  // ── 10 Indicator Scoring ──
  const indicators = [];

  // 1. EMA Ribbon
  let emaScore = 50, emaStatus = 'neutral';
  if (price > ema21 && ema9 > ema21 && ema21 > ema50) {
    emaScore = price > ema200 ? 92 : 78;
    emaStatus = 'bullish';
  } else if (price < ema21 && ema9 < ema21 && ema21 < ema50) {
    emaScore = price < ema200 ? 8 : 22;
    emaStatus = 'bearish';
  } else if (price > ema21) {
    emaScore = 65;
    emaStatus = 'bullish';
  } else {
    emaScore = 35;
    emaStatus = 'bearish';
  }
  indicators.push({
    name: 'EMA Ribbon (9/21/50)',
    weight: weights.ema,
    score: emaScore,
    status: emaStatus,
    detail: `P: ${price.toFixed(0)} | E21: ${ema21.toFixed(0)}`,
    note: emaStatus === 'bullish' ? 'Golden alignment' : 'Death alignment',
  });

  // 2. MACD
  let macdScore = 50, macdStatus = 'neutral';
  if (macdLine > macdSig && macdHist > 0) {
    const rising = macdHist > macdHistPrev;
    macdScore = rising ? 88 : 72;
    macdStatus = 'bullish';
  } else if (macdLine < macdSig && macdHist < 0) {
    const falling = macdHist < macdHistPrev;
    macdScore = falling ? 12 : 28;
    macdStatus = 'bearish';
  }
  indicators.push({
    name: 'MACD (12/26/9)',
    weight: weights.macd,
    score: macdScore,
    status: macdStatus,
    detail: `Hist: ${macdHist.toFixed(1)} | Line: ${macdLine.toFixed(1)}`,
    note: macdStatus === 'bullish' ? 'Bullish momentum' : macdStatus === 'bearish' ? 'Bearish momentum' : 'Converging',
  });

  // 3. RSI
  let rsiScore = 50, rsiStatus = 'neutral';
  if (rsiV >= 52 && rsiV <= 68) { rsiScore = 82; rsiStatus = 'bullish'; }
  else if (rsiV > 75) { rsiScore = 45; rsiStatus = 'neutral'; }
  else if (rsiV <= 48 && rsiV >= 32) { rsiScore = 18; rsiStatus = 'bearish'; }
  else if (rsiV < 25) { rsiScore = 55; rsiStatus = 'neutral'; }
  indicators.push({
    name: 'RSI (14)',
    weight: weights.rsi,
    score: rsiScore,
    status: rsiStatus,
    detail: `RSI: ${rsiV.toFixed(1)}`,
    note: rsiV > 70 ? 'Overbought zone' : rsiV < 30 ? 'Oversold zone' : 'Normal range',
  });

  // 4. StochRSI
  let stochScore = 50, stochStatus = 'neutral';
  if (stoch.k > stoch.d && stoch.k < 75) {
    stochScore = stoch.k < 35 ? 92 : 75;
    stochStatus = 'bullish';
  } else if (stoch.k < stoch.d && stoch.k > 25) {
    stochScore = stoch.k > 65 ? 8 : 22;
    stochStatus = 'bearish';
  }
  indicators.push({
    name: 'StochRSI (14/3/3)',
    weight: weights.stoch,
    score: stochScore,
    status: stochStatus,
    detail: `K: ${stoch.k.toFixed(0)} / D: ${stoch.d.toFixed(0)}`,
    note: stochStatus === 'bullish' ? 'Bullish cross' : stochStatus === 'bearish' ? 'Bearish cross' : 'Neutral',
  });

  // 5. Bollinger Bands
  let bbScore = 50, bbStatus = 'neutral';
  if (bbPctB > 60 && bbPctB < 92) { bbScore = 78; bbStatus = 'bullish'; }
  else if (bbPctB >= 95) { bbScore = 48; bbStatus = 'neutral'; }
  else if (bbPctB < 40 && bbPctB > 8) { bbScore = 22; bbStatus = 'bearish'; }
  else if (bbPctB <= 5) { bbScore = 50; bbStatus = 'neutral'; }
  indicators.push({
    name: 'Bollinger Bands (20/2)',
    weight: weights.bb,
    score: bbScore,
    status: bbStatus,
    detail: `%B: ${bbPctB.toFixed(0)}%`,
    note: bbBandwidth < 3.5 ? 'Squeeze compression' : 'Normal expansion',
  });

  // 6. ADX
  let adxScore = 50, adxStatus = 'neutral';
  const isTrending = adxData.adx >= 24;
  if (isTrending) {
    if (adxData.plusDI > adxData.minusDI) { adxScore = 86; adxStatus = 'bullish'; }
    else { adxScore = 14; adxStatus = 'bearish'; }
  }
  indicators.push({
    name: 'ADX (14)',
    weight: weights.adx,
    score: adxScore,
    status: adxStatus,
    detail: `ADX: ${adxData.adx.toFixed(0)} | +DI:${adxData.plusDI.toFixed(0)}`,
    note: isTrending ? `Trending (${adxData.adx.toFixed(0)})` : `Sideways (${adxData.adx.toFixed(0)})`,
  });

  // 7. VWAP
  let vwapScore = 50, vwapStatus = 'neutral';
  if (price > vwap && isHighVol) { vwapScore = 88; vwapStatus = 'bullish'; }
  else if (price > vwap) { vwapScore = 68; vwapStatus = 'bullish'; }
  else if (price < vwap && isHighVol) { vwapScore = 12; vwapStatus = 'bearish'; }
  else { vwapScore = 32; vwapStatus = 'bearish'; }
  indicators.push({
    name: 'VWAP & Volume',
    weight: weights.vwap,
    score: vwapScore,
    status: vwapStatus,
    detail: `VWAP: ${vwap.toFixed(0)}`,
    note: isHighVol ? 'High volume conviction' : 'Normal volume',
  });

  // 8. Volume Momentum
  let volScore = 50, volStatus = 'neutral';
  if (isHighVol && emaStatus === 'bullish') { volScore = 85; volStatus = 'bullish'; }
  else if (isHighVol && emaStatus === 'bearish') { volScore = 15; volStatus = 'bearish'; }
  else if (isLowVol) { volScore = 45; volStatus = 'neutral'; }
  indicators.push({
    name: 'Volume Momentum',
    weight: weights.volume,
    score: volScore,
    status: volStatus,
    detail: `Vol: ${formatVolume(currVol)}`,
    note: isHighVol ? 'Above average' : isLowVol ? 'Below average' : 'Normal volume',
  });

  // 9. Divergence
  let divScore = 50, divStatus = 'neutral';
  if (divergence.type === 'bullish' || divergence.type === 'hidden-bullish') {
    divScore = 78 + divergence.strength * 0.18;
    divStatus = 'bullish';
  } else if (divergence.type === 'bearish' || divergence.type === 'hidden-bearish') {
    divScore = 22 - divergence.strength * 0.18;
    divStatus = 'bearish';
  }
  indicators.push({
    name: 'Divergence Detector',
    weight: weights.divergence,
    score: clamp(divScore, 5, 95),
    status: divStatus,
    detail: divergence.type === 'none' ? 'No divergence' : divergence.type,
    note: divergence.reason || 'Clear oscillator',
  });

  // 10. Macro EMA 200
  let macroScore = 50, macroStatus = 'neutral';
  if (price > ema200) { macroScore = 82; macroStatus = 'bullish'; }
  else { macroScore = 18; macroStatus = 'bearish'; }
  indicators.push({
    name: 'Macro EMA 200',
    weight: weights.macro,
    score: macroScore,
    status: macroStatus,
    detail: `EMA200: ${ema200.toFixed(0)}`,
    note: price > ema200 ? 'Bullish macro structure' : 'Bearish macro structure',
  });

  // ── Weighted Consensus Scoring ──
  let totalWeight = 0;
  let weightedScore = 0;
  let bullish = 0, bearish = 0, neutral = 0;

  for (const ind of indicators) {
    weightedScore += (ind.score - 50) * (ind.weight / 100);
    totalWeight += ind.weight;
    if (ind.status === 'bullish') bullish++;
    else if (ind.status === 'bearish') bearish++;
    else neutral++;
  }

  const normScore = weightedScore * 2;
  const agreement = Math.max(bullish, bearish) / indicators.length;
  const regimeFactor = marketRegime === 'trending' ? 1.12 : marketRegime === 'range' ? 0.88 : marketRegime === 'volatile' ? 0.96 : 0.9;
  const trendingFactor = isTrending ? 1.12 : 0.88;
  const divPenalty = divergence.strength > 60 ? 0.88 : 1;
  const conflict = (bullish >= 4 && bearish >= 3) || (bearish >= 4 && bullish >= 3);

  let rawConfidence = (Math.abs(normScore) * 0.6 + agreement * 100 * 0.4) * trendingFactor * regimeFactor * divPenalty;
  if (conflict) rawConfidence *= 0.75;

  const confidence = Math.round(clamp(rawConfidence, 25, 98));

  return {
    price,
    indicators,
    confidence,
    normScore,
    bullishCount: bullish,
    bearishCount: bearish,
    neutralCount: neutral,
    atr: atrVal,
    adx: adxData,
    macd: { line: macdLine, signal: macdSig, hist: macdHist },
    rsi: rsiV,
    stoch,
    bbPctB,
    bbBandwidth,
    ema9, ema21, ema50, ema200,
    vwap,
    divergence,
    volProfile,
    keyLevels,
    isTrending,
    marketRegime,
    confirmation: getSignalConfirmation({
      isTrending,
      macd: { line: macdLine, signal: macdSig },
      stoch,
      ema9,
      ema21,
      volProfile,
      price,
    }),
  };
}

// ══════════════════════════════════════════════════════
// 9. MASTER SIGNAL GENERATOR (Multi-TF + Cache)
// ══════════════════════════════════════════════════════

async function getOrFetchTfCandles(tf) {
  const now = Date.now();
  const cached = state.tfCache[tf];
  const ttl = CONFIG.TF_CACHE_TTL[tf] || 60000;

  if (cached && cached.candles && cached.candles.length >= CONFIG.MIN_CANDLES && (now - cached.timestamp < ttl)) {
    return cached;
  }

  try {
    const data = await fetchBinanceRest(tf, 80);
    if (data && data.candles && data.candles.length >= CONFIG.MIN_CANDLES) {
      state.tfCache[tf] = {
        candles: data.candles,
        ticker: data.ticker,
        source: data.source,
        timestamp: now,
      };
      return state.tfCache[tf];
    }
  } catch (err) {
    // Fall back to stale cache if available
    if (cached && cached.candles) return cached;
  }
  return null;
}

async function generateMasterSignal(opts = {}) {
  const tfResults = {};
  let masterNorm = 0;
  let masterConf = 0;
  let totalUsed = 0;

  // 1. Current interval as primary
  const primaryResult = analyzeTimeframe(state.candles, state.interval);
  if (primaryResult) {
    const primaryWeight = TF_WEIGHTS[state.interval] || 0.4;
    tfResults[state.interval] = primaryResult;
    masterNorm += primaryResult.normScore * primaryWeight;
    masterConf += primaryResult.confidence * primaryWeight;
    totalUsed += primaryWeight;
  }

  // 2. Multi-timeframe analysis across all other intervals
  for (const [tf, weight] of Object.entries(TF_WEIGHTS)) {
    if (tf === state.interval) continue;

    const tfData = await getOrFetchTfCandles(tf);
    if (tfData && tfData.candles && tfData.candles.length >= CONFIG.MIN_CANDLES) {
      const result = analyzeTimeframe(tfData.candles, tf);
      if (result) {
        tfResults[tf] = result;
        masterNorm += result.normScore * weight;
        masterConf += result.confidence * weight;
        totalUsed += weight;
      }
    }
  }

  if (totalUsed === 0) return null;

  masterNorm /= totalUsed;
  masterConf /= totalUsed;
  const confidence = Math.round(clamp(masterConf, 25, 98));

  // Validation gates
  const primaryConfirmation = getSignalConfirmation(primaryResult);
  const performanceSummary = state.performance && state.performance.totalSignals > 0
    ? {
        winRate: (state.performance.wins / state.performance.totalSignals) * 100,
        profitFactor: Number(state.performance.profitFactor || 1),
      }
    : { winRate: 0, profitFactor: 1 };

  const validationThreshold = evaluateSignalThresholds(performanceSummary);
  const strictConfidenceGate = validationThreshold.confidenceFloor || 60;
  const validationReasons = [];
  const regimeBias = Math.abs(primaryResult?.normScore || 0);

  if (!primaryConfirmation.valid) validationReasons.push('confirmation');
  if (primaryResult?.marketRegime === 'range' && regimeBias < 12) validationReasons.push('range-weak');
  if (primaryResult?.marketRegime === 'volatile' && regimeBias < 18) validationReasons.push('volatile-noise');
  if (confidence < strictConfidenceGate) validationReasons.push('confidence-floor');
  if (Math.abs(masterNorm) < 15) validationReasons.push('insufficient-bias');

  const shouldWaitForConfirmation = validationReasons.length > 0;

  // Signal labeling
  let signalType, signalClass, badgeIcon, convictionLevel, guidance;

  if (shouldWaitForConfirmation) {
    signalType = 'WAIT (NEUTRAL)'; signalClass = 'neutral'; badgeIcon = '⏸️';
    convictionLevel = `ตลาดรอการยืนยัน ${confidence}% — รอนอกตลาด`;
    guidance = 'สัญญาณยังไม่ผ่านเกณฑ์การยืนยันครบถ้วน ความชัดเจนของตลาดยังไม่เพียงพอ ควรรอแท่งเทียน Breakout หรือ Confirmation ที่สมบูรณ์เพื่อป้องกัน False Signal';
  } else if (masterNorm >= 15) {
    if (confidence >= 82) {
      signalType = 'STRONG BUY'; signalClass = 'strong-buy'; badgeIcon = '⚡';
      convictionLevel = `ความมั่นใจสูงมาก ${confidence}% — เข้าได้ทันที`;
      guidance = 'สัญญาณ Bullish คอนเฟิร์มทุกมิติทั้ง Trend, Momentum, Volume และ Multi-Timeframe แนะนำเปิด Long ตามแผนและวาง Stop Loss เคร่งครัด';
    } else if (confidence >= 65) {
      signalType = 'BUY'; signalClass = 'buy'; badgeIcon = '🚀';
      convictionLevel = `สัญญาณชัดเจน ${confidence}% — เข้าเทรดได้`;
      guidance = 'อินดิเคเตอร์ส่วนใหญ่สนับสนุนขาขึ้น โครงสร้างราคาสามารถเข้าซื้อที่ระดับ Entry พร้อมตั้ง TP1/TP2 ตามลำดับ';
    } else if (confidence >= 48) {
      signalType = 'MODERATE BUY'; signalClass = 'buy'; badgeIcon = '📈';
      convictionLevel = `สัญญาณปานกลาง ${confidence}% — รอคอนเฟิร์ม`;
      guidance = 'เริ่มมีสัญญาณซื้อ แต่น้ำหนักยังไม่เต็มร้อย แนะนำแบ่งไม้เข้า หรือรอแท่งเทียนปิดยืนยันแนวรับ';
    } else {
      signalType = 'WEAK BUY'; signalClass = 'weak-caution'; badgeIcon = '⚠️';
      convictionLevel = `ความมั่นใจต่ำ ${confidence}% — ใช้ความระมัดระวัง`;
      guidance = 'สัญญาณซื้ออ่อน ยังมีความขัดแย้งระหว่าง Indicator แนะนำชะลอการเข้าออเดอร์';
    }
  } else if (masterNorm <= -15) {
    if (confidence >= 82) {
      signalType = 'STRONG SELL'; signalClass = 'strong-sell'; badgeIcon = '⚡';
      convictionLevel = `แรงขายรุนแรง ${confidence}% — Short / ขายทันที`;
      guidance = 'สัญญาณ Bearish คอนเฟิร์มทุก Timeframe โมเมนตัมขาลงรุนแรง แนะนำเปิด Short หรือปิดสถานะ Long ทั้งหมด';
    } else if (confidence >= 65) {
      signalType = 'SELL'; signalClass = 'sell'; badgeIcon = '🔻';
      convictionLevel = `สัญญาณชัดเจน ${confidence}% — ขาย / Short`;
      guidance = 'แรงขายมีน้ำหนักเหนือกว่า ตลาดหลุดแนวรับย่อย แนะนำพิจารณาฝั่ง Short';
    } else if (confidence >= 48) {
      signalType = 'MODERATE SELL'; signalClass = 'sell'; badgeIcon = '📉';
      convictionLevel = `สัญญาณขายปานกลาง ${confidence}% — ระวัง`;
      guidance = 'มีแรงกดดันขายเริ่มเด่นชัดขึ้น แนะนำลดความเสี่ยงหรือตั้งจุดตัดขาดทุนให้กระชับ';
    } else {
      signalType = 'WEAK SELL'; signalClass = 'weak-caution'; badgeIcon = '⚠️';
      convictionLevel = `ความมั่นใจต่ำ ${confidence}% — รอดูสถานการณ์`;
      guidance = 'สัญญาณขายอ่อน ยังมีความผันผวนสูง ควรรอการยืนยันแท่งเทียนถัดไป';
    }
  } else {
    signalType = 'WAIT (NEUTRAL)'; signalClass = 'neutral'; badgeIcon = '⏸️';
    convictionLevel = `ตลาดไซด์เวย์ ${confidence}% — รอนอกตลาด`;
    guidance = 'ตลาดไร้ทิศทางชัดเจน สัญญาณขัดแย้งระหว่าง Indicator แนะนำถือเงินสดรอกรอบ Breakout';
  }

  // Summary per timeframe
  const tfSummary = Object.entries(tfResults).map(([tf, r]) => ({
    tf,
    confidence: r.confidence,
    normScore: r.normScore,
    signal: r.normScore > 10 ? 'Bull' : r.normScore < -10 ? 'Bear' : 'Neutral',
    strength: r.isTrending ? 'Trending' : 'Sideways',
  }));

  const compositeAnalysis = {
    ...primaryResult,
    dataSource: state.dataHealth?.source || 'unknown',
    signalType,
    signalClass,
    badgeIcon,
    convictionLevel,
    guidance,
    confidence,
    normScore: masterNorm,
    tradeReady: !shouldWaitForConfirmation,
    validationReasons,
    validationThreshold,
    strictConfidenceGate,
    tfResults,
    tfSummary,
    timestamp: Date.now(),
  };

  // Compute profit setup — DOM values only when no explicit opts are given
  // (keeps the function unit-testable without a browser document).
  const capital = Number(opts.capital) || Number($('capitalInput')?.value) || 1000;
  const riskPct = Number(opts.riskPct) || Number($('riskInput')?.value) || 1.5;
  state.profitSetup = calcProfitOpportunity(compositeAnalysis, capital, riskPct, opts.performance);

  return compositeAnalysis;
}

// ══════════════════════════════════════════════════════
// 10. WEBSOCKET ENGINE (Watchdog & Smart Reconnection)
// ══════════════════════════════════════════════════════

function getWebSocketUrl(interval) {
  return `${CONFIG.WEBSOCKET_URL}?streams=btcusdt@kline_${interval}/btcusdt@ticker`;
}

function startWebSocket() {
  cleanupWebSocket();

  const url = getWebSocketUrl(state.interval);
  updateConnectionStatus('connecting');

  try {
    state.ws = new WebSocket(url);
  } catch (err) {
    console.warn('[WS] Constructor error:', err);
    scheduleReconnect();
    startFallbackPolling();
    return;
  }

  state.ws.onopen = () => {
    state.wsReconnectAttempts = 0;
    state.wsStatus = 'connected';
    state.wsLastTick = Date.now();
    updateConnectionStatus('live');
    stopFallbackPolling();
    startWatchdog();
  };

  state.ws.onmessage = (event) => {
    try {
      const msg = JSON.parse(event.data);
      processWsMessage(msg);
    } catch (e) {
      // Ignore malformed packets
    }
  };

  state.ws.onerror = () => {
    // onclose will follow
  };

  state.ws.onclose = () => {
    if (state.wsStatus !== 'disconnected') {
      state.wsStatus = 'disconnected';
      updateConnectionStatus('reconnecting');
      stopWatchdog();
      scheduleReconnect();
      startFallbackPolling();
    }
  };
}

function startWatchdog() {
  stopWatchdog();
  state.wsWatchdogTimer = setInterval(() => {
    if (state.wsStatus === 'connected' && (Date.now() - state.wsLastTick > 15000)) {
      console.warn('[WS] Watchdog: connection silent > 15s. Reconnecting...');
      cleanupWebSocket();
      startWebSocket();
    }
  }, 5000);
}

function stopWatchdog() {
  if (state.wsWatchdogTimer) {
    clearInterval(state.wsWatchdogTimer);
    state.wsWatchdogTimer = null;
  }
}

function processWsMessage(msg) {
  const { stream, data } = msg;
  if (!data) return;

  const now = Date.now();

  // 24hr ticker
  if (stream && stream.includes('@ticker')) {
    state.ticker.price = parseFloat(data.c) || state.ticker.price;
    state.ticker.change = parseFloat(data.p) || 0;
    state.ticker.changePercent = parseFloat(data.P) || 0;
    state.ticker.high24 = parseFloat(data.h) || 0;
    state.ticker.low24 = parseFloat(data.l) || 0;
    state.ticker.volume24 = parseFloat(data.v) || 0;
  }

  // Kline update
  if (stream && stream.includes('@kline') && data.k) {
    const k = data.k;
    const tickPrice = parseFloat(k.c);
    const candleTime = k.t;

    state.wsLatency = Math.max(5, now - state.wsLastTick);
    state.wsLastTick = now;
    state.wsTickCount++;

    if (state.wsPrevPrice !== null && tickPrice !== state.wsPrevPrice) {
      flashPrice(tickPrice > state.wsPrevPrice ? 'up' : 'down');
    }
    state.wsPrevPrice = tickPrice;
    state.ticker.price = tickPrice;

    if (state.candles.length > 0) {
      const last = state.candles[state.candles.length - 1];
      if (last.time === candleTime) {
        last.close = tickPrice;
        last.high = Math.max(last.high, parseFloat(k.h));
        last.low = Math.min(last.low, parseFloat(k.l));
        last.volume = parseFloat(k.v);
      } else if (candleTime > last.time) {
        state.candles.push({
          time: candleTime,
          open: parseFloat(k.o),
          high: parseFloat(k.h),
          low: parseFloat(k.l),
          close: tickPrice,
          volume: parseFloat(k.v),
        });
        if (state.candles.length > CONFIG.MAX_CANDLES) {
          state.candles.splice(0, state.candles.length - CONFIG.MAX_CANDLES);
        }
      }
    }

    scheduleAnalysis();
  }
}

function scheduleReconnect() {
  clearTimeout(state.wsReconnectTimer);
  state.wsReconnectAttempts++;

  const delay = Math.min(
    CONFIG.RECONNECT_BASE_DELAY * Math.pow(1.5, state.wsReconnectAttempts - 1),
    CONFIG.RECONNECT_MAX_DELAY
  );
  const jitter = delay * CONFIG.RECONNECT_JITTER * Math.random();

  state.wsReconnectTimer = setTimeout(() => startWebSocket(), delay + jitter);
}

function cleanupWebSocket() {
  clearTimeout(state.wsReconnectTimer);
  stopWatchdog();
  if (state.ws) {
    try {
      state.ws.onclose = null;
      state.ws.close();
    } catch (e) {}
    state.ws = null;
  }
}

function startFallbackPolling() {
  if (state.wsFallbackTimer) return;
  state.wsFallbackTimer = setInterval(() => {
    if (state.wsStatus !== 'connected') {
      refreshData();
    }
  }, CONFIG.FALLBACK_POLL_INTERVAL);
}

function stopFallbackPolling() {
  clearInterval(state.wsFallbackTimer);
  state.wsFallbackTimer = null;
}

// ══════════════════════════════════════════════════════
// 11. REST API FETCH & FALLBACK
// ══════════════════════════════════════════════════════

async function fetchBinanceRest(interval = '1h', limit = 120) {
  // Global concurrency gate: never fire more than MAX_INFLIGHT_FETCHES REST
  // calls at once (avoids Binance 429 on multi-timeframe refreshes / fallback
  // polling racing each other).
  await fetchGate.acquire();

  const controller = typeof AbortController !== 'undefined' ? new AbortController() : null;
  const timeout = controller ? setTimeout(() => controller.abort(), CONFIG.API_TIMEOUT) : null;

  try {
    const fetchOptions = controller ? { signal: controller.signal } : {};
    const [klineRes, tickerRes] = await Promise.all([
      fetch(`${CONFIG.REST_BASE}/klines?symbol=BTCUSDT&interval=${interval}&limit=${limit}`, fetchOptions),
      fetch(`${CONFIG.REST_BASE}/ticker/24hr?symbol=BTCUSDT`, fetchOptions),
    ]);

    if (timeout) clearTimeout(timeout);

    if (!klineRes.ok || !tickerRes.ok) throw new Error(`HTTP Error`);

    const klineData = await klineRes.json();
    const tickerData = await tickerRes.json();

    const candles = klineData.map(item => ({
      time: item[0],
      open: parseFloat(item[1]),
      high: parseFloat(item[2]),
      low: parseFloat(item[3]),
      close: parseFloat(item[4]),
      volume: parseFloat(item[5]),
    }));

    const ticker = {
      price: parseFloat(tickerData.lastPrice),
      change: parseFloat(tickerData.priceChange),
      changePercent: parseFloat(tickerData.priceChangePercent),
      high24: parseFloat(tickerData.highPrice),
      low24: parseFloat(tickerData.lowPrice),
      volume24: parseFloat(tickerData.volume),
    };

    const payload = { candles, ticker, source: 'Binance API' };
    const health = assessMarketData({ candles, ticker, source: 'Binance API', interval });
    if (!health.valid) {
      console.warn('[REST] Data validation failed, using fallback:', health.reason);
      return generateFallbackData(interval, limit);
    }
    return payload;

  } catch (err) {
    if (timeout) clearTimeout(timeout);
    return generateFallbackData(interval, limit);
  } finally {
    fetchGate.release();
  }
}

// ── Simple async semaphore used to cap concurrent REST fetches. ──
class PromiseGate {
  constructor(maxConcurrent = 2) {
    this.maxConcurrent = maxConcurrent;
    this.active = 0;
    this.queue = [];
  }
  acquire() {
    return new Promise(resolve => {
      if (this.active < this.maxConcurrent) {
        this.active += 1;
        resolve();
      } else {
        this.queue.push(resolve);
      }
    });
  }
  release() {
    this.active -= 1;
    const next = this.queue.shift();
    if (next) {
      this.active += 1;
      next();
    }
  }
}
const fetchGate = new PromiseGate(2);

function generateFallbackData(interval = '1h', count = 120) {
  let close = 82500;
  const now = Date.now();
  const stepMap = { '15m': 900000, '1h': 3600000, '4h': 14400000, '1d': 86400000 };
  const step = stepMap[interval] || 3600000;

  const candles = [];
  for (let i = 0; i < count; i++) {
    const time = now - (count - 1 - i) * step; // last candle is at 'now'
    const wave = Math.sin(i / 5) * 380 + Math.cos(i / 11) * 220;
    const shock = (i % 13 === 0) ? (Math.random() > 0.5 ? 280 : -250) : 0;
    const open = close;
    close = Math.max(65000, Math.min(120000, open + 35 + wave * 0.18 + shock));
    const high = Math.max(open, close) + 100 + Math.random() * 180;
    const low = Math.min(open, close) - 100 - Math.random() * 150;
    const volume = 20000 + Math.abs(wave) * 50 + Math.random() * 8000;
    candles.push({ time, open, high, low, close, volume });
  }

  const last = candles[candles.length - 1];
  const first = candles[0];
  const chg = last.close - first.close;
  const fallbackPayload = {
    candles,
    ticker: {
      price: last.close,
      change: chg,
      changePercent: (chg / first.close) * 100,
      high24: Math.max(...candles.map(c => c.high)),
      low24: Math.min(...candles.map(c => c.low)),
      volume24: candles.reduce((s, c) => s + c.volume, 0),
    },
    source: 'Simulated (offline)',
  };

  state.dataHealth = assessMarketData({ candles, ticker: fallbackPayload.ticker, source: fallbackPayload.source, interval });
  return fallbackPayload;
}

// ══════════════════════════════════════════════════════
// 12. RENDER PIPELINE (RAF Throttled)
// ══════════════════════════════════════════════════════

function scheduleAnalysis() {
  if (state.renderScheduled) return;
  state.renderScheduled = true;

  if (typeof requestAnimationFrame === 'function') {
    requestAnimationFrame(async () => {
      state.renderScheduled = false;
      const now = Date.now();
      if (now - state.lastRenderTime < CONFIG.RENDER_THROTTLE_MS) return;
      state.lastRenderTime = now;

      if (state.candles.length >= CONFIG.MIN_CANDLES) {
        state.analysis = await generateMasterSignal();
        if (state.analysis) {
          renderFullDashboard();
          updateConnectionMetrics();
        }
      }
    });
  }
}

async function refreshData() {
  if (state.isFetching) return;
  state.isFetching = true;

  const btn = $('refreshButton');
  if (btn) btn.classList.add('loading');

  try {
    const data = await fetchBinanceRest(state.interval);
    if (data) {
      state.candles = data.candles;
      state.ticker = data.ticker;
      state.dataHealth = assessMarketData({ candles: data.candles, ticker: data.ticker, source: data.source, interval: state.interval });

      if (!state.dataHealth.valid) {
        state.analysis = null;
        if (btn) btn.classList.add('data-warning');
        renderDataBanner(); // Surface the warning even when no analysis is rendered
        return;
      }

      state.analysis = await generateMasterSignal();
      if (state.analysis) renderFullDashboard();
    }
  } catch (err) {
    console.error('[Data] Refresh error:', err);
  } finally {
    state.isFetching = false;
    if (btn) setTimeout(() => btn.classList.remove('loading'), 300);
  }
}

// ══════════════════════════════════════════════════════
// 13. UI RENDERERS
// ══════════════════════════════════════════════════════

function getValidationReasonText(reason) {
  const map = {
    confirmation: 'confirmation missing',
    'range-weak': 'weak range structure',
    'volatile-noise': 'volatile noise',
    'confidence-floor': 'confidence below threshold',
    'insufficient-bias': 'insufficient directional bias',
    'weak-performance': 'weak historical performance',
  };
  return map[reason] || reason;
}

function renderDataBanner() {
  const banner = $('dataBanner');
  if (!banner || typeof document === 'undefined') return;

  const health = state.dataHealth || {};
  const source = String(health.source || '');
  const isSimulated = /simulat|offline|demo/i.test(source);
  const isBad = health.valid === false || isSimulated;

  if (!isBad) {
    banner.hidden = true;
    return;
  }

  banner.hidden = false;
  banner.classList.remove('warning', 'error');

  if (isSimulated && health.valid === false) {
    banner.classList.add('error');
    if ($('dataBannerTitle')) $('dataBannerTitle').textContent = '⚠️ กำลังใช้ข้อมูลจำลอง (Simulated Data)';
    if ($('dataBannerDetail')) $('dataBannerDetail').textContent =
      'ไม่สามารถเชื่อมต่อ Binance API ได้ สัญญาณ/กำไรที่แสดงมาจากข้อมูลจำลอง — ห้ามใช้เทรดจริงจนกว่าการเชื่อมต่อจะกลับคืนมา';
  } else if (isSimulated) {
    banner.classList.add('warning');
    if ($('dataBannerTitle')) $('dataBannerTitle').textContent = '⚠️ ข้อมูลจำลอง (Simulated Source)';
    if ($('dataBannerDetail')) $('dataBannerDetail').textContent =
      'แหล่งข้อมูลเป็นข้อมูลจำลอง offline ตัวเลขกำไร/E$ เป็นเพียงการสาธิต ไม่ใช่ข้อมูลตลาดจริง';
  } else {
    banner.classList.add('error');
    if ($('dataBannerTitle')) $('dataBannerTitle').textContent = '⚠️ ข้อมูลผิดปกติ (Data Warning)';
    if ($('dataBannerDetail')) $('dataBannerDetail').textContent = health.reason || 'ข้อมูลอาจล้าสมัยหรือไม่สมบูรณ์ โปรดตรวจสอบการเชื่อมต่อ';
  }
}

function renderFullDashboard() {
  const a = state.analysis;
  const t = state.ticker;
  if (!a) return;

  // Title
  if (typeof document !== 'undefined') {
    document.title = `₿ $${t.price.toFixed(0)} | ${a.signalType} (${a.confidence}%)`;
  }

  // Data integrity / fallback-source warning banner
  renderDataBanner();

  // 1. Live Price Card
  if ($('price')) $('price').textContent = t.price.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 });

  const isPos = t.change >= 0;
  if ($('priceChange')) {
    $('priceChange').className = `change ${isPos ? 'positive' : 'negative'}`;
    $('priceChange').innerHTML = `<span>${isPos ? '▲' : '▼'}</span> ${isPos ? '+' : ''}${t.change.toFixed(2)} (${isPos ? '+' : ''}${t.changePercent.toFixed(2)}%) <em>24H</em>`;
  }

  if ($('high24')) $('high24').textContent = formatMoney(t.high24);
  if ($('low24')) $('low24').textContent = formatMoney(t.low24);
  if ($('volume24')) $('volume24').textContent = `${(t.volume24 / 1000).toFixed(1)}K BTC`;
  if ($('atrValue')) $('atrValue').textContent = `±$${a.atr.toFixed(0)}`;

  // 2. Action Advice Banner
  const banner = $('actionBanner');
  if (banner) banner.className = `action-banner ${a.signalClass}`;
  if ($('actionBadge')) {
    $('actionBadge').textContent = a.signalType;
    $('actionBadge').className = `action-badge ${a.signalClass}`;
  }
  if ($('actionConviction')) $('actionConviction').textContent = a.convictionLevel;
  if ($('actionGuidance')) $('actionGuidance').textContent = a.guidance;
  if ($('actionIcon')) $('actionIcon').textContent = a.badgeIcon;

  const readinessText = a.tradeReady ? 'READY • ENTRY ALLOWED' : 'WAIT • NO ENTRY YET';
  const readinessColor = a.tradeReady ? 'var(--neon-green)' : '#ffb020';
  const reasonText = a.validationReasons && a.validationReasons.length
    ? `Reason: ${a.validationReasons.map(getValidationReasonText).join(' • ')}`
    : 'Reason: baseline checks passed';

  if ($('tradeReadiness')) {
    $('tradeReadiness').textContent = readinessText;
    $('tradeReadiness').style.color = readinessColor;
    $('tradeReadiness').style.borderColor = readinessColor;
    $('tradeReadiness').style.background = a.tradeReady ? 'rgba(0, 242, 173, 0.08)' : 'rgba(255, 176, 32, 0.08)';
  }
  if ($('validationSummary')) $('validationSummary').textContent = reasonText;

  // 3. Signal Decision Card
  if ($('signalText')) {
    $('signalText').textContent = a.signalType;
    $('signalText').className = a.signalClass;
  }
  if ($('signalBadgeIcon')) $('signalBadgeIcon').textContent = a.badgeIcon;
  if ($('signalSub')) $('signalSub').textContent = `${a.bullishCount} Bull vs ${a.bearishCount} Bear | ADX: ${a.adx.adx.toFixed(0)}`;
  if ($('signalDescription')) $('signalDescription').textContent = a.guidance;

  if ($('bullishCount')) $('bullishCount').textContent = a.bullishCount;
  if ($('neutralCount')) $('neutralCount').textContent = a.neutralCount;
  if ($('bearishCount')) $('bearishCount').textContent = a.bearishCount;

  // 4. Confidence Gauge
  if ($('confidenceValue')) $('confidenceValue').textContent = a.confidence;
  const gauge = $('gaugeValue');
  if (gauge) gauge.style.strokeDasharray = `${a.confidence} 100`;

  let gaugeColor, confLabel, confColor;
  if (a.confidence >= 80) {
    gaugeColor = '#00f2ad'; confLabel = 'High Conviction (เชื่อถือได้สูง)'; confColor = '#00f2ad';
  } else if (a.confidence >= 65) {
    gaugeColor = '#22d3a5'; confLabel = 'Reliable Signal (น่าเชื่อถือ)'; confColor = '#22d3a5';
  } else if (a.confidence >= 48) {
    gaugeColor = '#e9bc67'; confLabel = 'Moderate Signal (ปานกลาง)'; confColor = '#e9bc67';
  } else {
    gaugeColor = '#ff4d6d'; confLabel = 'Low Conviction (อ่อนแอ/ขัดแย้ง)'; confColor = '#ff4d6d';
  }

  if (gauge) gauge.style.stroke = gaugeColor;
  if ($('confidenceDot')) $('confidenceDot').style.background = gaugeColor;
  if ($('confidenceLabel')) {
    $('confidenceLabel').textContent = confLabel;
    $('confidenceLabel').style.color = confColor;
  }
  if ($('confidenceEval')) $('confidenceEval').textContent = `Score ${a.confidence}/100`;

  // 5. Consensus Bar & Indicator List
  if ($('consensusScore')) $('consensusScore').textContent = `${a.confidence}/100`;
  const cBar = $('consensusBar');
  if (cBar) {
    cBar.style.width = `${a.confidence}%`;
    cBar.style.background = `linear-gradient(90deg, ${gaugeColor}88, ${gaugeColor})`;
  }

  renderIndicatorList(a);
  renderMultiTFSummary(a);
  renderRiskManagement(a);
  renderPerformanceMetrics(a);
  renderInsights(a);

  // 6. Custom SVG Chart
  if (state.chartView === 'custom') {
    renderCustomChart(state.candles, a);
  }
}

function renderIndicatorList(analysis) {
  const listEl = $('indicatorList');
  if (!listEl) return;
  listEl.innerHTML = analysis.indicators.map(ind => `
    <div class="indicator-row">
      <div class="ind-main">
        <div class="ind-header">
          <span class="ind-name">${ind.name} <span class="ind-weight">(${ind.weight}%)</span></span>
          <span class="ind-badge ${ind.status}">${ind.status.toUpperCase()}</span>
        </div>
        <div class="ind-track">
          <div class="ind-fill ${ind.status}" style="width: ${ind.score}%"></div>
        </div>
      </div>
      <div class="ind-details">
        <span class="ind-val">${ind.detail}</span>
        <span class="ind-note">${ind.note}</span>
      </div>
    </div>
  `).join('');
}

function renderMultiTFSummary(analysis) {
  if (!analysis.tfSummary || analysis.tfSummary.length === 0) return;
  const container = $('multiTFSummary');
  if (!container) return;

  container.innerHTML = analysis.tfSummary.map(tf => {
    const cls = tf.signal === 'Bull' ? 'bullish' : tf.signal === 'Bear' ? 'bearish' : 'neutral';
    const icon = tf.signal === 'Bull' ? '🟢' : tf.signal === 'Bear' ? '🔴' : '⚪';
    return `
      <div class="tf-card ${cls}">
        <div class="tf-header">
          <span class="tf-name">${tf.tf}</span>
          <span class="tf-badge ${cls}">${icon} ${tf.signal}</span>
        </div>
        <div class="tf-stats">
          <span>Conf: ${tf.confidence}%</span>
          <span>${tf.strength}</span>
        </div>
      </div>
    `;
  }).join('');
  container.style.display = 'grid';
}

function renderRiskManagement(analysis) {
  const setup = state.profitSetup || calcProfitOpportunity(
    analysis,
    Number($('capitalInput')?.value) || 1000,
    Number($('riskInput')?.value) || 1.5
  );

  const price = analysis.price;
  const rb = $('riskBadge');

  if (!analysis.tradeReady || !setup) {
    if ($('bannerEntry')) $('bannerEntry').textContent = formatMoney(price);
    if ($('bannerStop')) $('bannerStop').textContent = 'WAIT';
    if ($('bannerTarget')) $('bannerTarget').textContent = 'WAIT';
    if ($('bannerTp2')) $('bannerTp2').textContent = 'WAIT';
    if ($('bannerTp3')) $('bannerTp3').textContent = 'WAIT';
    if ($('bannerEv')) $('bannerEv').textContent = '—';

    if ($('entryLevel')) $('entryLevel').textContent = '—';
    if ($('entrySub')) $('entrySub').textContent = 'No entry: waiting for confirmation';

    if ($('stopLevel')) $('stopLevel').textContent = '—';
    if ($('stopDiff')) $('stopDiff').textContent = '—';

    if ($('tp1Level')) $('tp1Level').textContent = '—';
    if ($('tp1Diff')) $('tp1Diff').textContent = '—';

    if ($('tp2Level')) $('tp2Level').textContent = '—';
    if ($('tp2Diff')) $('tp2Diff').textContent = '—';

    if ($('tp3Level')) $('tp3Level').textContent = '—';
    if ($('tp3Diff')) $('tp3Diff').textContent = '—';

    if ($('evLevel')) $('evLevel').textContent = '—';
    if ($('evDiff')) $('evDiff').textContent = 'รอสัญญาณที่ชัดเจน';

    if ($('positionBtc')) $('positionBtc').textContent = '— BTC';
    if ($('positionUsd')) $('positionUsd').textContent = '— USD';
    if ($('maxLossUsd')) $('maxLossUsd').textContent = '—';
    if ($('rrValue')) $('rrValue').textContent = '—';

    if ($('setupTypeTag')) $('setupTypeTag').textContent = '⏸️ SETUP: MARKET STANDBY';
    if ($('playbookText')) $('playbookText').textContent = 'ระบบบล็อกการเข้าเทรดชั่วคราวเนื่องจากความเสี่ยงยังไม่คุ้มค่า หรือสัญญาณยังขัดแย้งกัน';

    if (rb) {
      rb.textContent = '⏸️ WAIT / NO ENTRY';
      rb.className = 'risk-badge yellow';
    }
    return;
  }

  // Banner quick stats
  if ($('bannerEntry')) $('bannerEntry').textContent = formatMoney(setup.price);
  if ($('bannerStop')) $('bannerStop').textContent = formatMoney(setup.stopLevel);
  if ($('bannerTarget')) $('bannerTarget').textContent = formatMoney(setup.tp1);
  if ($('bannerTp2')) $('bannerTp2').textContent = formatMoney(setup.tp2);
  if ($('bannerTp3')) $('bannerTp3').textContent = formatMoney(setup.tp3);
  if ($('bannerEv')) {
    $('bannerEv').textContent = `+$${setup.expectedValueUsd.toFixed(1)}`;
    $('bannerEv').className = setup.expectedValueUsd > 0 ? 'color-blue' : 'color-red';
  }

  // Risk boxes
  if ($('entryLevel')) $('entryLevel').textContent = formatMoney(setup.price);
  if ($('entrySub')) $('entrySub').textContent = setup.isBuy ? 'Long Entry (ซื้อ)' : 'Short Entry (ขาย)';

  if ($('stopLevel')) $('stopLevel').textContent = formatMoney(setup.stopLevel);
  if ($('stopDiff')) $('stopDiff').textContent = `SL: ${formatMoney(setup.slDist)} (${((setup.slDist / price) * 100).toFixed(2)}%)`;

  if ($('tp1Level')) $('tp1Level').textContent = formatMoney(setup.tp1);
  if ($('tp1Diff')) $('tp1Diff').textContent = `TP1: +${formatMoney(setup.tp1Dist)} (1.5R)`;

  if ($('tp2Level')) $('tp2Level').textContent = formatMoney(setup.tp2);
  if ($('tp2Diff')) $('tp2Diff').textContent = `TP2: +${formatMoney(setup.tp2Dist)} (2.8R)`;

  if ($('tp3Level')) $('tp3Level').textContent = formatMoney(setup.tp3);
  if ($('tp3Diff')) $('tp3Diff').textContent = `TP3: +${formatMoney(setup.tp3Dist)} (4.5R Runner)`;

  if ($('evLevel')) $('evLevel').textContent = `+$${setup.expectedValueUsd.toFixed(2)}`;
  if ($('evDiff')) $('evDiff').textContent = `+${setup.expectedValueR.toFixed(2)}R ต่อไม้ (Win ${(setup.winProb * 100).toFixed(0)}%)`;

  if ($('positionBtc')) $('positionBtc').textContent = `${setup.positionBtc.toFixed(4)} BTC`;
  if ($('positionUsd')) $('positionUsd').textContent = formatMoney(setup.positionUsd);
  if ($('maxLossUsd')) $('maxLossUsd').textContent = `-$${setup.usedLossUsd.toFixed(2)}`;
  if ($('rrValue')) $('rrValue').textContent = `1 : ${setup.rrRatio}`;

  // Playbook & trailing stop
  if ($('setupTypeTag')) $('setupTypeTag').textContent = setup.setupType;
  if ($('playbookText')) $('playbookText').textContent = setup.trailingRule;

  if (rb) {
    if (analysis.confidence >= 75) {
      rb.textContent = '✅ HIGH EDGE / LOW RISK';
      rb.className = 'risk-badge green';
    } else if (analysis.confidence >= 50) {
      rb.textContent = '⚖️ BALANCED RISK';
      rb.className = 'risk-badge yellow';
    } else {
      rb.textContent = '⚠️ SPECULATIVE';
      rb.className = 'risk-badge red';
    }
  }
}

function renderPerformanceMetrics(analysis) {
  const perf = state.performance || { totalSignals: 0, wins: 0, losses: 0, avgR: 0, profitFactor: 1, maxDrawdown: 0 };
  const total = perf.totalSignals;
  const winRate = total ? (perf.wins / total) * 100 : 0;
  const recentRate = analysis?.confidence || 0;

  // Derive edge/quality from real tracked history when available.
  const hist = perf.history || [];
  const realAvgR = Number.isFinite(perf.avgR) ? perf.avgR : 0;
  const profitFactor = Number.isFinite(perf.profitFactor) ? perf.profitFactor : 1;
  const maxDD = Number.isFinite(perf.maxDrawdown) ? perf.maxDrawdown : 0;

  // Weighted multi-TF agreement based on the current composite analysis.
  const tfCount = Array.isArray(analysis?.tfSummary) ? analysis.tfSummary.length : 4;
  const agreements = (analysis?.tfSummary || []).filter(tf => tf && tf.signal !== undefined && tf.signal !== 'Neutral').length;

  const metrics = [
    { label: 'System Edge', value: `${total ? winRate.toFixed(1) : (recentRate * 0.75).toFixed(1)}%` },
    { label: 'Avg R:R Multiplier', value: `${realAvgR > 0 ? realAvgR.toFixed(2) : '1:2.4'}R` },
    { label: 'Profit Factor', value: `${Number.isFinite(profitFactor) && profitFactor > 0 ? profitFactor.toFixed(2) : '1.00'}x` },
    { label: 'Signal Quality', value: `${recentRate}%` },
    { label: 'Max Drawdown Cap', value: `${maxDD > 0 ? maxDD.toFixed(2) : '0.00'}R` },
    { label: 'Multi-TF Agreement', value: `${agreements}/${tfCount} TF` },
  ];

  const panel = $('performanceMetrics');
  if (!panel) return;

  panel.innerHTML = metrics.map(metric => `
    <div class="performance-tile">
      <small>${metric.label}</small>
      <strong>${metric.value}</strong>
    </div>
  `).join('');
}

function renderValidationGuard(analysis) {
  if (analysis?.tradeReady) {
    return {
      type: 'positive',
      icon: '✅',
      title: 'Trade Readiness: READY TO EXECUTE',
      desc: 'ข้อมูลมีความครบถ้วน สัญญาณทางเทคนิคและสถิติผ่านเกณฑ์ความคุ้มค่า สามารถเข้าทำกำไรตามจุด Entry ที่ระบุ',
    };
  }
  return {
    type: 'warning',
    icon: '⏸️',
    title: 'Trade Readiness: WAIT FOR CONFIRMATION',
    desc: analysis?.validationReasons?.length
      ? `ยังไม่อนุญาตให้เปิด Order: ${analysis.validationReasons.map(getValidationReasonText).join(' • ')}`
      : 'ตลาดอยู่ในสภาวะสับสน แนะนำรอยืนยันเพื่อรักษาเงินทุน',
  };
}

function renderDecisionPolicy(analysis) {
  if (!analysis) return null;
  return analysis.tradeReady ? {
    type: 'positive',
    icon: '🛡️',
    title: 'Decision Policy: Entry Approved',
    desc: `ผ่านเกณฑ์ความแม่นยำขั้นต่ำ (Floor: ${analysis.strictConfidenceGate}%) อัตราทดความเสี่ยงมีความได้เปรียบ (Positive Expectancy)`,
  } : {
    type: 'warning',
    icon: '🚦',
    title: 'Decision Policy: Entry Protected',
    desc: 'ระบบบล็อกคำสั่งซื้อขายอัตโนมัติ เพื่อป้องกันการเทรดในจุด Overbought/Oversold ที่ยังไร้โมเมนตัมยืนยัน',
  };
}

function renderInsights(analysis) {
  const insights = [renderValidationGuard(analysis), renderDecisionPolicy(analysis)].filter(Boolean);

  // 1. Trend insight
  if (analysis.price > analysis.ema21 && analysis.ema9 > analysis.ema21) {
    insights.push({ type: 'positive', icon: '↗️', title: 'Trend: ขาขึ้นแข็งแกร่ง (Bullish)',
      desc: `ราคาอยู่เหนือเส้น EMA 21 ($${analysis.ema21.toFixed(0)}) และ EMA 9/21/50 เรียงตัวแบบ Golden Alignment` });
  } else if (analysis.price < analysis.ema21 && analysis.ema9 < analysis.ema21) {
    insights.push({ type: 'danger', icon: '↘️', title: 'Trend: ขาลงชัดเจน (Bearish)',
      desc: `ราคาถูกกดต่ำกว่าเส้น EMA 21 ($${analysis.ema21.toFixed(0)}) แรงขายครองตลาด โครงสร้างฝั่งลงได้เปรียบ` });
  } else {
    insights.push({ type: 'warning', icon: '⚖️', title: 'Trend: ก้ำกึ่ง (Consolidation)',
      desc: `ราคาวิ่งผันผวนรอบเส้น EMA 21 ($${analysis.ema21.toFixed(0)}) สัญญาณเทรนด์กำลังทดสอบแนวต้าน/แนวรับ` });
  }

  // 2. Momentum synergy
  if (analysis.macd.line > analysis.macd.signal && analysis.stoch.k > analysis.stoch.d) {
    insights.push({ type: 'positive', icon: '⚡', title: 'Momentum: ขาขึ้นสอดคล้อง',
      desc: `MACD Histogram (+${analysis.macd.hist.toFixed(1)}) และ StochRSI Golden Cross ชี้ขึ้นพร้อมกัน` });
  } else if (analysis.macd.line < analysis.macd.signal && analysis.stoch.k < analysis.stoch.d) {
    insights.push({ type: 'danger', icon: '🔻', title: 'Momentum: ขาลงสอดคล้อง',
      desc: `MACD Histogram (${analysis.macd.hist.toFixed(1)}) และ StochRSI Death Cross ยืนยันแรงขายอย่างต่อเนื่อง` });
  } else {
    insights.push({ type: 'warning', icon: '⚖️', title: 'Momentum: สัญญาณขัดแย้ง',
      desc: 'โมเมนตัมระยะสั้นและระยะกลางยังให้ภาพขัดแย้งกัน แนะนำใช้ความระมัดระวังเป็นพิเศษ' });
  }

  // 3. ADX & Market State
  if (analysis.isTrending) {
    insights.push({ type: 'positive', icon: '🎯', title: `Trend Strength: ADX ${analysis.adx.adx.toFixed(0)} (Strong Trend)`,
      desc: 'ความแรงของเทรนด์อยู่ในระดับสูง อัตราความแม่นยำของอินดิเคเตอร์ตามเทรนด์จะสูงขึ้นอย่างมีนัยสำคัญ' });
  } else {
    insights.push({ type: 'warning', icon: '🌊', title: `Market State: ADX ${analysis.adx.adx.toFixed(0)} (Sideways)`,
      desc: 'ตลาดขาดโมเมนตัมทิศทางหลัก False Breakout เกิดขึ้นได้บ่อยครั้ง แนะนำเน้น TP1 สั้นๆ' });
  }

  // 4. Divergence
  if (analysis.divergence && analysis.divergence.type !== 'none') {
    const isBull = analysis.divergence.type.includes('bullish');
    insights.push({
      type: isBull ? 'positive' : 'danger',
      icon: '🔍',
      title: `Divergence Alert: ${analysis.divergence.type.toUpperCase()}`,
      desc: `ตรวจพบสัญญาณ ${analysis.divergence.type} (${analysis.divergence.strength}% conviction) — ${analysis.divergence.reason}`,
    });
  }

  // 5. Multi-TF
  if (analysis.tfSummary) {
    const bulls = analysis.tfSummary.filter(t => t.signal === 'Bull').length;
    const bears = analysis.tfSummary.filter(t => t.signal === 'Bear').length;
    if (bulls >= 3) {
      insights.push({ type: 'positive', icon: '📊', title: 'Multi-TF: Bullish Consensus (3+ Timeframes)',
        desc: 'กราฟ Timeframe ใหญ่และย่อยเห็นพ้องต้องกัน โอกาสทำกำไรฝั่ง Long สูงสุด' });
    } else if (bears >= 3) {
      insights.push({ type: 'danger', icon: '📊', title: 'Multi-TF: Bearish Consensus (3+ Timeframes)',
        desc: 'กราฟ Timeframe ส่วนใหญ่ชี้ลงตรงกัน โครงสร้างขาลงมีน้ำหนักครอบคลุม' });
    }
  }

  const listEl = $('insightList');
  if (listEl) {
    listEl.innerHTML = insights.map(item => `
      <div class="insight ${item.type}">
        <span class="insight-icon">${item.icon}</span>
        <div>
          <strong>${item.title}</strong>
          <p>${item.desc}</p>
        </div>
      </div>
    `).join('');
  }
}

// ══════════════════════════════════════════════════════
// 14. CUSTOM SVG CHART (With Volume Histogram & TP/SL Levels)
// ══════════════════════════════════════════════════════

function renderCustomChart(candles, analysis) {
  const layer = $('candleLayer');
  const volLayer = $('volumeLayer');
  const levelsLayer = $('levelsLayer');
  const gridLines = $('gridLines');
  const yAxis = $('yAxis');
  const xAxis = $('xAxis');

  if (!layer || !candles.length || !analysis) return;

  const data = candles.slice(-50);
  const highs = data.map(c => c.high);
  const lows = data.map(c => c.low);
  const volumes = data.map(c => c.volume);

  const minVal = Math.min(...lows) * 0.997;
  const maxVal = Math.max(...highs) * 1.003;
  const range = maxVal - minVal || 1;
  const maxVol = Math.max(...volumes) || 1;

  const H = 290, W = 800;
  const chartHeight = H - 35; // leave space for bottom volume bars
  const volMaxH = 45;

  const getY = v => chartHeight - ((v - minVal) / range) * (chartHeight - 30) - 10;
  const getX = i => (i / (data.length - 1)) * (W - 20) + 10;
  const cw = Math.max(3, Math.min(10, (W / data.length) * 0.65));

  // Grid
  if (gridLines) {
    gridLines.innerHTML = [0.2, 0.4, 0.6, 0.8].map(r => {
      const y = chartHeight * r;
      return `<line x1="0" y1="${y}" x2="${W}" y2="${y}" stroke="rgba(42,70,60,0.3)" stroke-dasharray="3,4"/>`;
    }).join('');
  }

  // Volume Histogram (Lower pane)
  if (volLayer) {
    volLayer.innerHTML = data.map((c, i) => {
      const cx = getX(i);
      const bull = c.close >= c.open;
      const col = bull ? 'rgba(0, 242, 173, 0.35)' : 'rgba(255, 77, 109, 0.35)';
      const barH = Math.max(2, (c.volume / maxVol) * volMaxH);
      const y = H - barH;
      return `<rect x="${cx - cw / 2}" y="${y}" width="${cw}" height="${barH}" fill="${col}" rx="1"/>`;
    }).join('');
  }

  // Candlesticks
  layer.innerHTML = data.map((c, i) => {
    const cx = getX(i);
    const oy = getY(c.open);
    const cy = getY(c.close);
    const hy = getY(c.high);
    const ly = getY(c.low);
    const bull = c.close >= c.open;
    const color = bull ? '#00f2ad' : '#ff4d6d';
    const top = Math.min(oy, cy);
    const bh = Math.max(2, Math.abs(cy - oy));
    return `
      <line x1="${cx}" y1="${hy}" x2="${cx}" y2="${ly}" stroke="${color}" stroke-width="1.2"/>
      <rect x="${cx - cw / 2}" y="${top}" width="${cw}" height="${bh}" fill="${color}" rx="1.5"/>
    `;
  }).join('');

  // EMA Lines (memoized — only recompute when the candle stack changes)
  const lastCandle = candles[candles.length - 1];
  const cacheKey = lastCandle ? `${lastCandle.time}:${candles.length}` : 'empty';
  let { e9, e21, e50 } = state.chartEmaCache;
  if (state.chartEmaCache.key !== cacheKey) {
    const closes = candles.map(c => c.close);
    e9 = calcEMA(closes, 9);
    e21 = calcEMA(closes, 21);
    e50 = calcEMA(closes, 50);
    state.chartEmaCache = { key: cacheKey, e9, e21, e50 };
  }

  const buildPath = (series) => {
    const pts = [];
    const arr = Array.from(series);
    for (let i = arr.length - data.length; i < arr.length; i++) {
      if (i >= 0 && !Number.isNaN(arr[i])) {
        pts.push(`${getX(i - (arr.length - data.length)).toFixed(1)},${getY(arr[i]).toFixed(1)}`);
      }
    }
    return pts.length ? `M ${pts.join(' L ')}` : '';
  };

  if ($('ema9Line')) $('ema9Line').setAttribute('d', buildPath(e9));
  if ($('ema21Line')) $('ema21Line').setAttribute('d', buildPath(e21));
  if ($('ema50Line')) $('ema50Line').setAttribute('d', buildPath(e50));

  // Profit Setup Levels (Entry, SL, TP1, TP2, TP3)
  if (levelsLayer) {
    const setup = state.profitSetup;
    const entryP = analysis.price;
    const slP = setup ? setup.stopLevel : (analysis.price - analysis.atr * 1.5);
    const tp1P = setup ? setup.tp1 : (analysis.price + analysis.atr * 1.5);
    const tp2P = setup ? setup.tp2 : (analysis.price + analysis.atr * 2.8);

    const entryY = getY(entryP);
    const slY = getY(slP);
    const tp1Y = getY(tp1P);
    const tp2Y = getY(tp2P);

    levelsLayer.innerHTML = `
      <!-- Entry Level -->
      <line x1="0" y1="${entryY}" x2="${W}" y2="${entryY}" stroke="#eaf5f1" stroke-dasharray="4,4" stroke-width="1.2" opacity="0.75"/>
      <rect x="8" y="${entryY - 14}" width="85" height="13" fill="#132420" rx="3" stroke="#eaf5f1" stroke-width="0.8"/>
      <text x="12" y="${entryY - 4}" fill="#eaf5f1" font-size="9" font-family="Space Grotesk">Entry: $${entryP.toFixed(0)}</text>

      <!-- Stop Loss Level -->
      <line x1="0" y1="${slY}" x2="${W}" y2="${slY}" stroke="#ff4d6d" stroke-dasharray="4,4" stroke-width="1.4"/>
      <rect x="8" y="${slY - 14}" width="78" height="13" fill="#2d1318" rx="3" stroke="#ff4d6d" stroke-width="0.8"/>
      <text x="12" y="${slY - 4}" fill="#ff4d6d" font-size="9" font-family="Space Grotesk">SL: $${slP.toFixed(0)}</text>

      <!-- TP1 Level -->
      <line x1="0" y1="${tp1Y}" x2="${W}" y2="${tp1Y}" stroke="#00f2ad" stroke-dasharray="4,4" stroke-width="1.4"/>
      <rect x="8" y="${tp1Y - 14}" width="85" height="13" fill="#0d2922" rx="3" stroke="#00f2ad" stroke-width="0.8"/>
      <text x="12" y="${tp1Y - 4}" fill="#00f2ad" font-size="9" font-family="Space Grotesk">TP1: $${tp1P.toFixed(0)}</text>

      <!-- TP2 Level -->
      <line x1="0" y1="${tp2Y}" x2="${W}" y2="${tp2Y}" stroke="#38bdf8" stroke-dasharray="3,3" stroke-width="1.2"/>
      <rect x="8" y="${tp2Y - 14}" width="85" height="13" fill="#0c202a" rx="3" stroke="#38bdf8" stroke-width="0.8"/>
      <text x="12" y="${tp2Y - 4}" fill="#38bdf8" font-size="9" font-family="Space Grotesk">TP2: $${tp2P.toFixed(0)}</text>
    `;
  }

  // Y axis
  if (yAxis) {
    yAxis.innerHTML = Array.from({ length: 5 }, (_, i) => {
      const val = maxVal - (range / 4) * i;
      return `<span>$${(val / 1000).toFixed(1)}K</span>`;
    }).join('');
  }

  // X axis
  if (xAxis) {
    const idxs = [0, Math.floor(data.length / 4), Math.floor(data.length / 2), Math.floor(3 * data.length / 4), data.length - 1];
    xAxis.innerHTML = idxs.map(i => {
      const d = new Date(data[i].time);
      return `<span>${d.toLocaleTimeString('th-TH', { hour: '2-digit', minute: '2-digit' })}</span>`;
    }).join('');
  }
}

// ══════════════════════════════════════════════════════
// 15. TRADINGVIEW WIDGET
// ══════════════════════════════════════════════════════

function initTradingView(interval = state.interval || '1h') {
  const container = $('tradingview_widget');
  if (!container) return;

  const tvIntervalMap = { '15m': '15', '1h': '60', '4h': '240', '1d': 'D' };
  const tvInt = tvIntervalMap[interval] || '60';

  container.innerHTML = '';

  if (typeof TradingView !== 'undefined') {
    try {
      state.tvWidget = new TradingView.widget({
        autosize: true,
        symbol: 'BINANCE:BTCUSDT',
        interval: tvInt,
        timezone: 'Asia/Bangkok',
        theme: 'dark',
        style: '1',
        locale: 'th_TH',
        toolbar_bg: '#08100f',
        enable_publishing: false,
        hide_side_toolbar: false,
        allow_symbol_change: false,
        details: false,
        hotlist: false,
        calendar: false,
        container_id: 'tradingview_widget',
        studies: ['MASimple@tv-basicstudies', 'RSI@tv-basicstudies', 'MACD@tv-basicstudies'],
        overrides: {
          'paneProperties.background': '#0b1614',
          'paneProperties.vertGridProperties.color': 'rgba(32, 60, 52, 0.4)',
          'paneProperties.horzGridProperties.color': 'rgba(32, 60, 52, 0.4)',
          'mainSeriesProperties.candleStyle.upColor': '#00f2ad',
          'mainSeriesProperties.candleStyle.downColor': '#ff4d6d',
          'mainSeriesProperties.candleStyle.borderUpColor': '#00f2ad',
          'mainSeriesProperties.candleStyle.borderDownColor': '#ff4d6d',
          'mainSeriesProperties.candleStyle.wickUpColor': '#00f2ad',
          'mainSeriesProperties.candleStyle.wickDownColor': '#ff4d6d',
        },
      });
    } catch (e) {
      container.innerHTML = `<iframe src="https://www.tradingview.com/widgetembed/?symbol=BINANCE%3ABTCUSDT&interval=${tvInt}&theme=dark&style=1&locale=th_TH" style="width:100%;height:100%;border:none;border-radius:10px;"></iframe>`;
    }
  }
}

// ══════════════════════════════════════════════════════
// 16. CONNECTION STATUS & METRICS
// ══════════════════════════════════════════════════════

function updateConnectionStatus(state_) {
  const statusEl = $('feedStatus');
  if (!statusEl) return;

  if (state_ === 'live') {
    statusEl.innerHTML = `
      <span class="live-badge-realtime">
        <span class="pulse-ring"></span>
        <span>WEBSOCKET LIVE</span>
      </span>
      <small id="lastUpdated">เชื่อมต่อสำเร็จ</small>
    `;
  } else if (state_ === 'connecting') {
    statusEl.innerHTML = `
      <span class="status-indicator" style="background:var(--amber);box-shadow:0 0 8px var(--amber);animation:pulse-dot 1.2s infinite;"></span>
      <span class="feed-text" style="color:var(--amber);">กำลังเชื่อมต่อ...</span>
      <small id="lastUpdated">รอสัญญาณ</small>
    `;
  } else {
    statusEl.innerHTML = `
      <span class="status-indicator" style="background:var(--neon-red);box-shadow:0 0 8px var(--neon-red);"></span>
      <span class="feed-text" style="color:var(--neon-red);">กำลังเชื่อมต่อใหม่...</span>
      <small id="lastUpdated">${state.wsReconnectAttempts > 1 ? `ครั้งที่ ${state.wsReconnectAttempts}` : 'Retrying...'}</small>
    `;
  }
}

function updateConnectionMetrics() {
  const el = $('lastUpdated');
  if (el) {
    const status = state.wsStatus === 'connected' ? '🟢' : '🟡';
    el.textContent = `${status} #${state.wsTickCount} • ${new Date().toLocaleTimeString('th-TH')}`;
  }
}

function flashPrice(direction) {
  const el = $('price');
  if (!el) return;
  clearTimeout(state.wsFlashTimer);
  el.classList.remove('price-flash-up', 'price-flash-down');
  void el.offsetWidth;
  el.classList.add(direction === 'up' ? 'price-flash-up' : 'price-flash-down');
  state.wsFlashTimer = setTimeout(() => {
    el.classList.remove('price-flash-up', 'price-flash-down');
  }, CONFIG.PRICE_FLASH_DURATION);
}

// ══════════════════════════════════════════════════════
// 17. BACKTESTING & PERFORMANCE TRACKING
// ══════════════════════════════════════════════════════

// Persist performance metrics + signal history to localStorage so that
// win-rate / profit-factor statistics survive page reloads (real edge data).
const STORAGE_KEY = 'btcusd_signal_pro_perf_v1';

function savePersistedState() {
  if (typeof localStorage === 'undefined' || !localStorage) return;
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(state.performance));
  } catch (e) {
    // Storage full / private mode — non-fatal, just skip persistence.
  }
}

function loadPersistedState() {
  if (typeof localStorage === 'undefined' || !localStorage) return;
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (!raw) return;
    const saved = JSON.parse(raw);
    if (saved && typeof saved === 'object' && Array.isArray(saved.history)) {
      // Merge saved counters, guarding against corrupted/missing fields.
      state.performance.totalSignals = Number(saved.totalSignals) || 0;
      state.performance.wins = Number(saved.wins) || 0;
      state.performance.losses = Number(saved.losses) || 0;
      state.performance.avgR = Number(saved.avgR) || 0;
      state.performance.profitFactor = Number.isFinite(Number(saved.profitFactor)) ? Number(saved.profitFactor) : 1;
      state.performance.maxDrawdown = Number(saved.maxDrawdown) || 0;
      state.performance.lastRun = Number(saved.lastRun) || Date.now();
      state.performance.history = saved.history.slice(0, 2000); // cap history size
    }
  } catch (e) {
    // Corrupted storage — ignore and start fresh.
  }
}

function recordSignalOutcome({ direction, entry, stop, takeProfit, confidence, regime, outcome }) {
  const pnl = typeof outcome === 'number' ? outcome : 0;
  const rMultiple = stop > 0 ? ((direction === 'long' ? (pnl / Math.abs(entry - stop)) : (pnl / Math.abs(stop - entry))) || 0) : 0;

  state.performance.history.push({
    direction,
    entry,
    stop,
    takeProfit,
    confidence,
    regime,
    outcome,
    rMultiple,
    at: Date.now(),
  });
  // Cap runtime history so the in-memory array cannot grow unbounded
  // (localStorage persistence caps at the same limit on reload).
  if (state.performance.history.length > 2000) {
    state.performance.history = state.performance.history.slice(-2000);
  }

  state.performance.totalSignals += 1;
  if (pnl > 0) state.performance.wins += 1;
  if (pnl < 0) state.performance.losses += 1;

  const arr = state.performance.history.map(item => item.rMultiple || 0);
  state.performance.avgR = arr.reduce((sum, val) => sum + val, 0) / (arr.length || 1);

  const grossWin = state.performance.history.filter(item => (item.outcome || 0) > 0).reduce((sum, item) => sum + (item.outcome || 0), 0);
  const grossLoss = Math.abs(state.performance.history.filter(item => (item.outcome || 0) < 0).reduce((sum, item) => sum + (item.outcome || 0), 0));
  state.performance.profitFactor = grossLoss > 0 ? grossWin / grossLoss : (grossWin > 0 ? Number.POSITIVE_INFINITY : 1);

  // Equity-curve max drawdown from signal history (peak-to-trough of P&L).
  let cur = 0, peak = 0, runningDrawdown = 0;
  for (const item of state.performance.history) {
    cur += (item.outcome || 0);
    if (cur > peak) peak = cur;
    const dd = peak - cur;
    if (dd > runningDrawdown) runningDrawdown = dd;
  }
  state.performance.maxDrawdown = runningDrawdown;
  state.performance.lastRun = Date.now();

  // Persist to localStorage so real edge survives reloads.
  savePersistedState();

  return state.performance;
}

function simulateBacktestFromCandles(candles, signalGenerator) {
  if (!Array.isArray(candles) || candles.length < CONFIG.MIN_CANDLES) return null;

  const feeRate = Number(CONFIG.FEE_RATE) || 0.001;
  const results = [];
  // Walk forward, but only permit a SL/TP touch within a bounded number of bars
  // (won't hold a position indefinitely). This is a more realistic OHLC-based
  // simulation than the previous close-to-close approach.
  const MAX_HOLD_BARS = 20;

  for (let i = 20; i < candles.length - 1; i++) {
    const slice = candles.slice(0, i + 1);
    const signal = signalGenerator(slice);
    if (!signal) continue;

    const direction = signal.direction;
    const entry = Number(signal.entry || signal.price || slice[slice.length - 1].close || 0);
    const stop = Number(signal.stop || (direction === 'long' ? entry * 0.99 : entry * 1.01));
    const target = Number(signal.target || (direction === 'long' ? entry * 1.015 : entry * 0.985));

    let exitPrice = null;
    let exitReason = '';
    let barCount = 0;

    for (let j = i + 1; j < candles.length && barCount < MAX_HOLD_BARS; j++, barCount++) {
      const bar = candles[j];
      const high = bar.high;
      const low = bar.low;
      const close = bar.close;

      if (direction === 'long') {
        // Stop loss hit first -> loss
        if (low <= stop) { exitPrice = stop; exitReason = 'sl'; break; }
        // Target hit first -> win
        if (high >= target) { exitPrice = target; exitReason = 'tp'; break; }
        // Bar closed below stop -> loss (market close below)
        if (close <= stop) { exitPrice = close; exitReason = 'sl'; break; }
      } else {
        if (high >= stop) { exitPrice = stop; exitReason = 'sl'; break; }
        if (low <= target) { exitPrice = target; exitReason = 'tp'; break; }
        if (close >= stop) { exitPrice = close; exitReason = 'sl'; break; }
      }
      exitPrice = close; // still holding at bar close; carry to next bar
      exitReason = 'hold';
    }

    // If never stopped-out within the window, close at final examined close.
    if (exitPrice === null) {
      const lastBar = candles[Math.min(i + MAX_HOLD_BARS, candles.length - 1)];
      exitPrice = lastBar.close;
      exitReason = 'time';
    }

    const grossPnl = direction === 'long' ? (exitPrice - entry) : (entry - exitPrice);
    // Notional fee drag — approximate a round-trip fee on the entry notional.
    const notional = Math.abs(entry);
    const feeCost = notional * feeRate;
    const netPnl = grossPnl - feeCost;

    results.push({
      direction,
      entry,
      stop,
      target,
      exitPrice,
      exitReason,
      outcome: netPnl,
      grossPnl,
      feeCost,
      confidence: signal.confidence,
      regime: signal.regime,
    });
  }
  return results;
}

function generateBacktestSummary(results = []) {
  if (!results || !results.length) {
    return { total: 0, winRate: 0, avgR: 0, profitFactor: 1, maxDrawdown: 0, status: 'no-data' };
  }

  const total = results.length;
  const wins = results.filter(item => (item.outcome || 0) > 0).length;
  const losses = results.filter(item => (item.outcome || 0) < 0).length;
  const winRate = (wins / total) * 100;

  const netProfit = results.reduce((sum, item) => sum + (item.outcome || 0), 0);
  const grossWin = results.filter(item => (item.outcome || 0) > 0).reduce((sum, item) => sum + (item.outcome || 0), 0);
  const grossLoss = Math.abs(results.filter(item => (item.outcome || 0) < 0).reduce((sum, item) => sum + (item.outcome || 0), 0));
  const profitFactor = grossLoss > 0 ? grossWin / grossLoss : (grossWin > 0 ? Number.POSITIVE_INFINITY : 1);
  const avgR = total ? netProfit / total : 0;

  // Equity-curve max drawdown: peak-to-trough of cumulative P&L (more honest
  // than taking the single worst loss — reflects capital erosion path).
  let cur = 0, peak = 0, maxDrawdown = 0;
  for (const item of results) {
    cur += (item.outcome || 0);
    if (cur > peak) peak = cur;
    const dd = peak - cur;
    if (dd > maxDrawdown) maxDrawdown = dd;
  }

  return {
    total,
    wins,
    losses,
    winRate,
    avgR,
    profitFactor,
    maxDrawdown,
    netProfit,
    status: winRate >= 50 && profitFactor >= 1.2 ? 'acceptable' : 'needs-tuning',
  };
}

// ══════════════════════════════════════════════════════
// 18. EVENTS & BOOTSTRAP
// ══════════════════════════════════════════════════════

function setupEvents() {
  $('refreshButton')?.addEventListener('click', () => {
    refreshData();
    cleanupWebSocket();
    startWebSocket();
  });

  document.querySelectorAll('#timeframeButtons button').forEach(btn => {
    btn.addEventListener('click', async () => {
      document.querySelectorAll('#timeframeButtons button').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      state.interval = btn.dataset.tf || '1h';

      initTradingView(state.interval);
      await refreshData();
      cleanupWebSocket();
      startWebSocket();
    });
  });

  $('btnViewTV')?.addEventListener('click', () => {
    $('btnViewTV')?.classList.add('active');
    $('btnViewCustom')?.classList.remove('active');
    if ($('tvContainer')) $('tvContainer').style.display = 'block';
    if ($('customChartContainer')) $('customChartContainer').style.display = 'none';
    state.chartView = 'tv';
  });

  $('btnViewCustom')?.addEventListener('click', () => {
    $('btnViewCustom')?.classList.add('active');
    $('btnViewTV')?.classList.remove('active');
    if ($('tvContainer')) $('tvContainer').style.display = 'none';
    if ($('customChartContainer')) $('customChartContainer').style.display = 'block';
    state.chartView = 'custom';
    if (state.candles.length && state.analysis) {
      renderCustomChart(state.candles, state.analysis);
    }
  });

  const onRiskParamChange = () => {
    if (state.analysis) {
      state.profitSetup = calcProfitOpportunity(
        state.analysis,
        Number($('capitalInput')?.value) || 1000,
        Number($('riskInput')?.value) || 1.5
      );
      renderRiskManagement(state.analysis);
    }
  };

  $('capitalInput')?.addEventListener('input', onRiskParamChange);
  $('riskInput')?.addEventListener('input', onRiskParamChange);

  if (typeof document !== 'undefined') {
    document.addEventListener('visibilitychange', () => {
      if (document.visibilityState === 'visible') {
        const elapsed = Date.now() - state.wsLastTick;
        if (elapsed > 20000 || state.wsStatus !== 'connected') {
          cleanupWebSocket();
          startWebSocket();
          refreshData();
        }
      }
    });
  }
}

if (typeof window !== 'undefined' && typeof window.addEventListener === 'function') {
  window.addEventListener('DOMContentLoaded', async () => {
    setupEvents();
    initTradingView();
    loadPersistedState(); // restore stat history before first render

    const data = await fetchBinanceRest(state.interval);
    if (data) {
      state.candles = data.candles;
      state.ticker = data.ticker;
      state.analysis = await generateMasterSignal();
      if (state.analysis) renderFullDashboard();
    }

    startWebSocket();
    console.log('🚀 BTC/USD PRO v3.3 AI Intelligence & Profit Engine Initialized');
  });
}

// ══════════════════════════════════════════════════════
// 19. MODULE EXPORTS (For Unit Testing & External Access)
// ══════════════════════════════════════════════════════

if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    CONFIG,
    state,
    assessMarketData,
    getDataHealthSummary,
    calcSMA,
    calcEMA,
    calcRSI,
    calcMACD,
    calcBB,
    calcATR,
    calcADX,
    calcVWAP,
    calcStochRSI,
    detectDivergence,
    calcVolumeProfile,
    detectKeyLevels,
    detectMarketRegime,
    getSignalConfirmation,
    calcProfitOpportunity,
    analyzeTimeframe,
    generateMasterSignal,
    recordSignalOutcome,
    simulateBacktestFromCandles,
    generateBacktestSummary,
    getWebSocketUrl,
    scheduleReconnect,
    updateConnectionStatus,
    startFallbackPolling,
    stopFallbackPolling,
  };
}