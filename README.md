# BTC/USD PRO v3.3 — AI Signal Engine & Risk Dashboard

Vanilla-JS real-time dashboard analyzing **BTCUSDT** on 4 timeframes (15m/1h/4h/1d),
combining 10 indicators, divergence detection, multi-TF weights, validation gates,
and a fee-aware Kelly position-sizing & expectancy engine.

## Features
- **Real-time feed**: Binance WebSocket (kline + 24hr ticker), 15s watchdog, exponential backoff reconnection, 3s REST fallback polling
- **Rate-limit protection**: REST concurrency cap (2 in-flight) + per-timeframe TTL cache
- **Data integrity**: freshness/age validation, simulated-data fallback + explicit UI warning banner
- **Indicators**: SMA/EMA (NaN-tolerant), RSI, MACD, StochRSI, BB, ATR, ADX, VWAP, Volume Profile, S/R & POC, divergence
- **Signal gates**: confidence floor adapts to real tracked win-rate; neutral/choppy → WAIT (no entry)
- **Profit engine**: 3-tier TP (1.5R/2.8R/4.5R), structural SL, **net-of-fee EV/break-even win rate**, realized-win-rate blended position sizing
- **Backtest**: OHLC bar-aware SL/TP with fee drag + equity-curve max drawdown summary
- **Persistence**: signal outcomes saved to localStorage (up to 2000 trades) — edge survives reload

## Run
Open `index.html` in a browser (needs internet for Binance).

## Test
```
npm test
```
5 suites: data-quality, indicators-and-strategy, performance-and-backtest,
master-signal-gates, reliability (WS reconnect/fallback/concurrency/drawdown).
