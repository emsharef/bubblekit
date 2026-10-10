# Extending the Local-Martingale Theory of Bubbles: Research Directions

*Working notes -- October 2026. Status labels: **[sketched]** = derivation exists but unaudited; **[conjecture]** = stated, not proved; **[open]** = question, no candidate answer yet.*

---

## 1. Starting point and the reframing

The Jarrow-Protter-Shimbo theory identifies a price bubble with the strict-local-martingale property of the discounted price under a pricing measure Q. The characterization is clean, but the property lives in the tail of the volatility function beyond any observed price, so every existing detector is "tail estimate + extrapolation rule," and the two hypotheses (true vs. strict local martingale) are not statistically separable at finite horizons.

The working stance of this program is to stop asking the binary question and work with objects that are finite-horizon and identified:

- **The bubble term structure.** For a traded maturity T,
  β_t(T) = S_t − e^{−r(T−t)} E^Q_t[S_T + dividends].
  This is the Q-supermartingale gap. It equals the strike-asymptote of the T-maturity call, lim_{K→∞} C_t(K,T), since puts carry no bubble and parity holds in market prices. It is bounded above by any traded far-OTM call price.
- **The hazard representation.** Under the share measure Q̃ (density S_T/S_0), β_t(T) = S_t · Q̃(explosion before T). Writing β_t(T) = S_t(1 − exp(−∫_t^T h_u du)) defines a *bubble hazard curve* h, with the same role a credit hazard curve plays.
- **Shape restrictions.** β_t(T)/S_t must be a distribution function in T; for fixed T, β_t(T) is a nonnegative Q-supermartingale in t hitting zero at T; the short-end slope is the Q-drift that enters the Jarrow-Kwok P/Q risk-premium decomposition.

Nothing in this section is deep. Its purpose is to make the theory testable against named alternatives (borrow cost, demand pressure) and usable at horizons an investor cares about. The depth is meant to come from Sections 2-4.

---

## 2. Theorems about portfolios, not assets

The observation that drives this section: **the bubble property belongs to a wealth process, not to an asset.** A cap-weighted index is a fixed basket between rebalances and inherits constituent bubbles linearly. A rebalanced portfolio is a stochastic integral, and stochastic integrals against local martingales can gain or lose the strict property.

### Theorem A -- strategy-induced bubbles **[sketched]**

Let dS = σ(S) dW under Q, driftless, and let V^π be the wealth of a constant-proportion strategy holding fraction π > 0 of wealth in S. Then

> V^π is a strict local martingale **iff** S is a strict local martingale **and** π > 1/2.

*Route.* V^π = V_0 · ℰ(π ∫ σ(S)/S dW). Mijatović-Urusov: ℰ(∫ b(Y) dW) for a 1-D diffusion Y fails to be a true martingale iff the Girsanov-shifted auxiliary diffusion explodes. Here the auxiliary SDE is dS = σ(S) dW̃ + π σ²(S)/S dt. Its scale density is exp(−∫ 2π/x) = x^{−2π}, independent of σ. Feller's explosion test at +∞ requires
v(∞) = ∫^∞ x^{−2π} ∫^x y^{2π}/σ²(y) dy dx < ∞,
and by Fubini v(∞) = (2π − 1)^{−1} ∫^∞ y/σ²(y) dy for π > 1/2, infinite for π ≤ 1/2. The remaining integral is the JKP bubble criterion for S. The zero boundary needs the standard check (auxiliary drift is positive, so it should be benign).

*Reading.* Buy-and-hold inherits the bubble; any rebalanced exposure at or below one-half of wealth has a bubble-free wealth process even while holding a bubbly asset; leverage inherits the bubble. The threshold is universal across volatility functions.

*To audit.* Optimal-investment-with-a-bubble papers (Herdegen-Schweizer and related) and the Karatzas-Ruf line on portfolios of strict local martingales, for a special case of this.

### Conjecture A′ -- diversification destroys bubbles **[conjecture]**

For N ≥ 3 names whose bubbles are driven by their own level-dependent volatilities, a constant-proportion portfolio is bubbly iff some name is bubbly and the portfolio's exposure to it under that name's share measure exceeds 1/2. In the fully idiosyncratic case this reduces to max_i π_i > 1/2, so the **equal-weight index of bubbly names is a true martingale while the cap-weighted index is not.**

Independence of the names may not be needed; where it is needed is part of what the proof would reveal.

### Direction B -- bubbles and stochastic portfolio theory **[open]**

The natural route to A′ is Fernholz's master equation: for a functionally generated portfolio with generating function G and excess growth rate γ*,
log(V^G_T / V^μ_T) = log G(μ_T)/G(μ_0) + ∫_0^T γ*_t dt.
γ* is a quadratic-variation object, hence measure-invariant. Taking expectations against the market's share measure relates the index bubble, the rebalanced portfolio's bubble, and E[∫γ*]. The tension is exact and economically meaningful: a concentrated bubble raises excess growth (good for the rebalanced portfolio) and destroys diversity (G falls as one name dominates). The theorem to find is the condition under which excess growth wins. SPT and the JPS theory both rest on strict local martingales and have never been connected at the constituent level.

---

## 3. Aggregation, dispersion, and identification

### Theorem C -- share-measure mixture **[sketched]**

For a fixed basket I = Σ n_i S_i under a common Q:

1. β_I(T) = Σ n_i β_i(T) -- exact linearity, no correlation input. This is the first-moment analog of dispersion trading, which rests on implied correlation.
2. The index share measure is a mixture of constituent share measures: dQ̃_I = Σ ω_i dQ̃_i with ω_i the initial weights. The index hazard curve is the ω-mixture of constituent hazard curves.
3. Under Q̃_I, a bubbly name's cap weight μ_i is a strict supermartingale whose deficit equals its bubble share: **bubbles are expected weight losses under the index numéraire.** Weights are bounded, so this reformulation has no tail at infinity; the identification problem moves entirely to the measure change.

### Theorem E -- bubble shares from weights **[conjecture, route clear]**

Suppose the pricing kernel is a function of the index level alone (one-factor SDF; relative performance among names is unpriced). Then conditional on I_T, the cross-sectional law of weights agrees under P, Q and Q̃_I, and

> bubble share of name i = μ_{i,0} − E_{Q̃_I}[ E_P(μ_{i,T} | I_T) ].

The inner term is a P-conditional expectation of a bounded variable, estimable from the price panel; the outer distribution is readable from SPX call prices (Q̃_I(I_T > K) ∝ C(K) + K ∂_K C). Single-name bubbles are thus identified from **single-name prices plus index options only**: no single-name surfaces, no American-exercise issue, no borrow data, no tail.

The identifying assumption is explicit and testable. Overidentifying checks come free: the estimator should be ~0 in quiet periods, and Σ n_i β̂_i should match the SPX asymptote by Theorem C. The index's own bubble has to be handled separately (Theorem C lets you).

### The bubble clock -- a local-time representation **[sketched]**

Under Q̃ the price has drift σ²(S)/S; the deterministic skeleton reaches infinity in time ∫_S^∞ x/σ²(x) dx, which is the JKP integral. So the criterion reads: *bubble iff finite time-to-the-top on the share-measure clock.*

By the occupation-time formula, over the visited range,
∫_a^b x/σ²(x) dx = ∫_0^t S_u / L_t^{S_u} du,
with L the semimartingale local time. The volatility function drops out: the visited part of the bubble integral is a pathwise functional of price and local time, estimable from intraday data with standard (Jacod; Jacod-Protter pre-averaging) tools. The unvisited tail still needs a frontier exponent, now estimated from local-time decay at the top of the range with a one-sided test rather than an extrapolation family. Pooling frontier exponents across names in a sector gives a fast sector-level statistic.

This is the sharpest price-only object the theory admits. It is not a verdict about the Q-bubble.

### Concentration and dependence **[open]**

Theorem C constrains the sum of constituent bubbles; the *distribution* of n_i β_i across names is new information. A concentration index distinguishes 2000-style (sector-concentrated) from broad episodes. Whether a bubble dissipates by rotation (index flat, leaders deflate) or by index drawdown is a dependence question -- do constituent bubbles burst together -- that Q-additivity does not answer. It is a credit-portfolio problem in disguise: names with hazard rates, a common frailty, Marshall-Olkin common shocks. The allocation implication (reduce concentration vs. reduce beta) is currently unavailable anywhere.

---

## 4. Scheduled events

Scheduled jumps (earnings, FOMC) cannot by themselves create a bubble: at a scheduled date the process satisfies a discrete-time martingale condition, and nonnegative discrete-time local martingales are true martingales (Jarrow-Protter 2012). Mass can only be lost in the diffusive segments between events. What events can do is place the process in a level where the subsequent diffusion explodes.

- **[sketched]** For a scheduled-jump process with level-dependent between-event volatility, the process on [0,T] is a true martingale iff each inter-event diffusion is a true martingale from every attainable post-jump level.
- **[conjecture]** The share-measure explosion distribution is absolutely continuous (size-biasing a jump with finite Q-mean gives a proper law) but can concentrate immediately after events: the hazard clusters, the term structure β_t(T) steps across the first expiry after an event. Earnings-day crash clustering is known on the P side; the Q-side hazard clustering is not.

This connects directly to the scheduled-jump forward-curve program, and the swap-rate version below uses the same machinery.

---

## 5. Fixed income: the well-posed version

Bounded payoffs (bonds, credit, MBS) cannot carry Type-3 bubbles. The live cases are perpetual/rollover claims (Type 1-2; the fiscal-theory debt-bubble debate, undetectable at finite horizons by construction), strict-local-martingale pricing kernels (Platen's benchmark school), and **rates as the underlying under a numéraire that makes them local martingales.**

Under the annuity measure the forward swap rate is a nonnegative local martingale; payers/receivers are the calls/puts; everything in Section 1 ports. Economically, β is a Q-internal wedge between the forward rate and the Q^A-expected future rate, distinct from the term premium -- giving a three-way decomposition of forward-minus-realized. Lognormal SABR with ρ > 0 is already a strict local martingale (Jourdain), and Andersen-Piterbarg's moment-explosion paper exists because desks calibrate such models; 2022-23 (vol rising with rates) is the natural episode. CMS replication and cap-vs-swaption additivity give extrapolation-free cross-checks. Data are in-house at any rates shop. This is a second project sharing method with the equity one.

---

## 6. Empirical and trading directions (unordered)

- **Additivity test.** Σ n_i β̂_i over the top 50-100 SPX names vs. the SPX asymptote, both with bound versions. Agreement supports a common Q in the far tail; a persistent gap is either dilution (FJL's "names yes, index no"), segmentation, or a *bubble-dispersion premium* -- the first-moment analog of the correlation risk premium. The trade is a basket of short deep-OTM single-name calls against long deep-OTM index calls; its P&L is a direct P-vs-Q test of the hazard (realized idiosyncratic explosions vs. implied).
- **Equal-weight vs. cap-weight.** Options trade on RSP and SPY. Conjecture A′ predicts the far-OTM call asymptote on RSP is ~0 in episodes where SPY's is positive. Nobody has looked.
- **Fingerprint test against the parity-violation literature.** Borrow cost: calls cheap vs. puts, flat in K, deep-OTM calls decay to zero. Demand pressure: gap concentrated at retail strikes. Bubble: calls rich vs. fundamental by β, flat in K, hazard-shaped in T, positive asymptote. Two predictions competing mechanisms do not make. The borrow bias runs the safe direction (ignoring it understates β).
- **Horizon-dependent expected returns.** E^P_t[S_T] − S_t e^{r(T−t)} = (premium term) − β_t(T) e^{r(T−t)}. An option-implied, horizon-specific drag per name or sector for a tactical process; tested as a crash forecaster (Brier/CRPS at 1-12 months) and a mean-return forecaster, against Cremers-Weinbaum spread, risk-neutral skew, SVIX, momentum, short interest.
- **Concentration → rotation vs. drawdown.** Price-only version via frontier exponents on CRSP (century-long); option-anchored version on 1996-2026.
- **Bubble clock as a monitor.** Rolling intraday "time to infinity" with confidence bands, with sector pooling.

Practical notes carried over: end-of-day OptionMetrics suffices for the equity work (FJL did it that way); parity-implied forward handles carry and borrow; short-dated OTM contracts keep early-exercise premium negligible; crypto is out of scope.

---

## 7. Open questions worth keeping visible

- Is the π = 1/2 threshold in Theorem A stable under stochastic volatility, or does the vol-of-vol move it? (The auxiliary-diffusion argument is 1-D; SV needs its own treatment.)
- In A′, does cross-name correlation matter at all, or only exposure under each name's share measure?
- Does Section 3's weight-based identification survive a two-factor kernel (index + sector)? If a sector factor is priced, what exactly does the estimator pick up?
- Is the bubble-dispersion gap, if it exists, compensated by realized explosions (a premium) or not (segmentation)? The answer decides whether it is a trade.
- Can the hazard-clustering-after-events prediction be sharpened into a bound on how much of β_t(T) can accrue in the first post-event expiry?
- For rates: does the Q-internal forward wedge survive once vendor SABR calibrations with ρ > 0 are replaced by a true-martingale alternative that fits the same cube? If so, the wedge is a market fact; if not, it is a modeling artifact.

---

## 8. Where one might start

Not a plan -- a list of things that are each a few pages and would each change the shape of what comes next:

1. Prove Theorem A cleanly, including the zero boundary and a stochastic-volatility remark.
2. Do the two-asset case of A′ with constant proportions (π_1, π_2) and find the exact true-martingale region.
3. Prove the local-time representation and write down the estimator's rate.
4. State Theorem E precisely (what σ-field the kernel must be measurable with respect to; how the index's own bubble enters) and prove it.
5. Pull RSP and SPY far-OTM call ladders for 2020-21 and 2024-26 and look at the asymptotes. This is a day's work and may settle whether A′ is worth a proof.

Whichever of these produces a surprise is the paper.
