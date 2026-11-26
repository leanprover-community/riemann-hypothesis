module

public import New.Congruences.Lifting.SidePoints
import New.Congruences.Lifting.SafeMoves

/-!
# Deep points and scaled cup coboundaries for a gap below zero or nonpositive jumps

A side `S` (`New.Lift.KummerChart.PairingSide`) has sets `S.jumpSet i` that hold the jumps at
each letter `i`. `S.pointsOver c i κ lo o` is the set of points over `p ^ κ c` at the letter `i`,
with orders `lo` and depth `o`. The steps from a depth `o` to a depth `o'` are the integers `y`
with `o l u ≤ y < o' l u`, each taken at its level `l`. The level `0` belongs to the prime `E` of
the chart `k`, and `d = k.differentBound`. This file raises the depth of points when all steps
occur at the level `0`, and bounds the cost of this with `New.Lift.KummerChart.cost`. It deduces
the cup conditions for paired sides in two cases: when no jump lies in `[-a, 0)`, and when the
chart is unramified and all jumps of the second side lie in `[-η, 0]`.

## Main definitions and results

* `New.Lift.KummerChart.PairingSide.sum_cost_eq_card_mul`: if no nonzero step is divisible by
  `p`, the total cost of any set of steps in the windows is its cardinality times the different
  bound.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_gap`,
  `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_jumps_nonpos`: the cup
  conditions when no jump lies in `[-a, 0)`, and when all jumps of `S'` lie in `[-η, 0]`.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_killsCokernel`: paired
  sides satisfy the cup conditions with exponent `H` when `3 κ + 2 (4 a + 4 η + W) d ≤ H`. The
  hypotheses are these. The cokernels are killed. The jumps lie in opposite windows. At every `i`,
  `p` divides no nonzero integer within `a + max a η + max η W` of `0` or `± b i`. Either no jump lies
  in `[-a, 0)`, or the chart is unramified and all jumps of `S'` lie in `[-η, 0]`.

Notions from other files:
* `New.Lift.KummerChart`: a Kummer chart `k` of the group `Γ` over `G_p`: a ring `Λ⟦z⟧` inside
  `A_inf` with a distinguished element `E` (`E = z + p` if the chart is unramified) and a subgroup
  `Γ'` of `Γ` of index prime to `p`. Its letters are the units of the residue field
  `𝔽_{p ^ k.f}`; a letter singles out embeddings of the coefficients, and `i.stepBack l` is the
  letter `l` steps of Frobenius before `i`.
* `New.Lift.KummerChart.PairingSide`: one side of a pairing: lattices `Y` and `paramLattice`, an
  `O`-linear map `cocycleMap` from `paramLattice` to the crystalline cocycles `Z_f(Y)`, and for each
  letter a finite set of integers that contains `0`. `S.extensionLattice` is the extension of the
  trivial lattice `paramLattice` by `Y` given by the cocycles of `S`, with the jump sets of `S`.
* Orders `o l u` prescribe, for every level `l` and jump `u` at `i.stepBack l`, a power of the
  uniformiser of `B_dR⁺` that divides the value of an element on the line `u` at the level `l`. An
  element has depth `o` if its differences with its translates by `Γ'` have orders `o`.
* `New.Lift.KummerChart.cost`: the cost `k.cost l n = v_p(n) + d + 3 l` of the step `n` at the level
  `l`, with `v_p(0) = 0`; here `d = 0` if the index `e` of the chart is `1`, and `d = v_p(e) + 1`
  otherwise.
* `New.Lift.KummerChart.PairingSide.KillsCokernel`: `p ^ κ * E ^ a` kills the cokernel at the letter
  `i`: it multiplies the letter-`i` part of `A_inf ⊗ C` into the image of the extension's module of
  standard exponents of level `0`.
* `New.Lift.FitsWindows`: `FitsWindows η ε b W U` says that `U` lies in the union of the low window
  `[-η, η]` and the far window `ε • [b, b + W]`.
* `New.Lift.Pairing.IsScaledCupCoboundary`: the cup conditions with exponent `H` for `c` and `c'`:
  the cup product of the cocycles `S.cocycleMap c` and `p ^ H • S'.cocycleMap c'` is a continuous
  coboundary.

## Relation to the literature

See `New.Congruences.Lifting.FewLowJumps` for related work.
-/

@[expose] public section

namespace New.Lift.KummerChart.PairingSide

open Finset JumpLattice Period Int

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
variable {k : KummerChart Γ} {O : Coeffs} {S S' : PairingSide O}

/-- Under the prime gap, each step in the three windows costs exactly the different bound. -/
lemma sum_cost_eq_card_mul {n : ℕ} {b : ℤ} {s : Finset ℤ} (h : NoMultipleNear p n b)
    (hs : s ⊆ twoWindows n b ∪ twoWindows n (-b)) :
    ∑ y ∈ s, k.cost 0 y = #s * k.differentBound := by
  refine sum_const_nat fun y hy ↦ ?_
  have h_zero := h.eq_zero_of_dvd (hs hy)
  have h_val : padicValInt p y = 0 := padicValInt.eq_zero_iff.2 (by tauto)
  simp [cost, h_val]

/-- The integers within `n` of `0`, `b` or `-b`, described by inequalities. -/
lemma mem_twoWindows_union_iff {n : ℕ} {b y : ℤ} :
    y ∈ twoWindows n b ∪ twoWindows n (-b) ↔
      -n ≤ y ∧ y ≤ n ∨ b - n ≤ y ∧ y ≤ b + n ∨ -b - n ≤ y ∧ y ≤ -b + n := by
  simp only [twoWindows, mem_union, mem_Icc]
  omega

/-- Deepening at the level `0`. Let the side `S` have a point over `p ^ κ • c` at the letter `i`
with exponents `lo` and depth `o`. If all steps `y` from `o` to the depth `o'` are at the level `0`
and lie in a set `steps` of total cost at most `stepCost`, then `S` has a point over
`p ^ (κ + stepCost) • c` at `i` with depth `o'` and exponents `improvedOrders lo o'` (that is, `o'`
where `lo` is positive and `min o' 0` elsewhere). -/
lemma pointsOver_nonempty_of_steps_level_zero {κ stepCost : ℕ} {i : k.Letter} {c : S.paramLattice}
    {lo o o' : ℕ → ℤ → ℤ} {steps : Finset ℤ} (h_point : (S.pointsOver c i κ lo o).Nonempty)
    (h_steps : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, o l u ≤ y → y < o' l u →
      l = 0 ∧ y ∈ steps)
    (h_cost : ∑ y ∈ steps, k.cost 0 y ≤ stepCost) :
    (S.pointsOver c i (κ + stepCost) (improvedOrders lo o') o').Nonempty := by
  obtain ⟨x, hx⟩ := h_point
  exact pointsOver_nonempty_of_costs hx (({0} : Finset ℕ).sigma fun _ ↦ steps)
    (by simpa using h_steps) (by simpa [sum_sigma] using h_cost)

private lemma steps_at_level_zero {a t : ℕ} {i : k.Letter} {steps : Finset ℤ}
    (h : ∀ u ∈ S.jumpSet i, Ico (-u - a) (a + t - u) ⊆ steps)
    (l : ℕ) (u : ℤ) (hu : u ∈ S.jumpSet (i.stepBack l)) (y : ℤ)
    (hlo : raisedOrdersAtZero (-a) l u ≤ y) (hhi : y < plainDepth a t 1 0 l u) :
    l = 0 ∧ y ∈ steps := by
  obtain ⟨rfl, hy⟩ : l = 0 ∧ -u - a ≤ y ∧ y < a + t - u := by
    dsimp only [raisedOrdersAtZero, plainDepth, standardDepth] at hlo hhi
    split_ifs at hlo hhi <;> omega
  exact ⟨rfl, h u hu (mem_Ico.2 hy)⟩

/-- Deep points under a gap below `0`. Let `p ^ κ * E ^ a` kill the cokernel of the side `S` at the
letter `i`. Let no jump lie in `[-a, 0)`, and let the set `steps` contain `[-u - a, a + η - u)` for
every jump `u` at `i`, with sum of the costs `k.cost 0 y = v_p(y) + k.differentBound` at most
`stepCost`. Then `S` has a point over `p ^ (κ + stepCost) • c` at `i` without pole and of depth
`plainDepth a η 1 0`, which is `a + η - u` at the level `0` and `-u` at the levels above. -/
lemma pointsOver_nonempty_of_gap {a κ η stepCost : ℕ} {i : k.Letter}
    (h_kill : S.KillsCokernel i κ a)
    (h_gap : ∀ u ∈ S.jumpSet i, u ∉ Ico (-a : ℤ) 0) {steps : Finset ℤ}
    (h_steps : ∀ u ∈ S.jumpSet i, Ico (-u - a) (a + η - u) ⊆ steps)
    (h_cost : ∑ y ∈ steps, k.cost 0 y ≤ stepCost) (c : S.paramLattice.Carrier) :
    (S.pointsOver c i (κ + stepCost) (raisedOrdersAtZero 0) (plainDepth a η 1 0)).Nonempty := by
  -- Deepen a point with a pole of order `a` along `steps`; by the gap the pole disappears.
  obtain ⟨x, hx⟩ : Set.Nonempty (S.pointsOver c i (κ + stepCost)
      (improvedOrders (raisedOrdersAtZero (-a)) (plainDepth a η 1 0)) (plainDepth a η 1 0)) :=
    pointsOver_nonempty_of_steps_level_zero (pointsOver_nonempty_of_killsCokernel h_kill c)
      (steps_at_level_zero h_steps) h_cost
  have h_nonneg : ∀ u ∈ S.jumpSet i, -(a : ℤ) ≤ u → -0 ≤ u := fun u hu h ↦ by
    have h' := h_gap u hu
    rw [mem_Ico] at h'
    omega
  have h_no_pole :
      x ∈ S.pointsOver c i (κ + stepCost) (raisedOrdersAtZero (-0)) (plainDepth a η 1 0) :=
    mem_pointsOver_raisedOrdersAtZero_of_gap hx le_rfl h_nonneg
      (fun l u _ ↦ by
        dsimp only [improvedOrders, raisedOrdersAtZero, plainDepth, standardDepth]
        split_ifs <;> omega)
      fun l u _ ↦ by
        dsimp only [improvedOrders, raisedOrdersAtZero, plainDepth, standardDepth]
        split_ifs <;> omega
  exact ⟨x, by simpa only [neg_zero] using h_no_pole⟩

private lemma mem_pointsOver_of_no_pole {i : k.Letter} {c : S.paramLattice} {e : ℕ}
    {d : ℕ → ℤ → ℤ} {x : S.extensionLattice.Ambient} (t : ℕ)
    (hx : x ∈ S.pointsOver c i e (raisedOrdersAtZero 0) d) :
    x ∈ S.pointsOver c i e (raisedOrdersAtZero (-t)) d :=
  mem_pointsOver_of_exponent_le hx fun l u _ ↦ raisedOrdersAtZero_mono (by omega) l u

/-- The scaled cup coboundary under a gap below `0`. Let `P` be a pairing of the lattices of the
sides `S` and `S'`, and `P.tateDualSide` the side on the Tate dual of their tensor product that
carries the pairing. Here a side is a lattice with a family of crystalline cocycles and, at each
letter `i` of the chart `k` (a unit of its residue field), a finite set `jumpSet i` of integers. At
every letter let `p ^ κ * E ^ a`, with `E` the distinguished element of the chart, kill the
cokernels of `S`, `S'` and `P.tateDualSide`. Let the jumps of `S` lie in `[-η, η]` or in
`-ε i • [b i, b i + W]`, those of `S'` in `[-η, η]` or in `ε i • [b i, b i + W]` for a sign
`ε i = ±1`, none of them in `[-a, 0)`. For each side, its step set contains `[-u - a, a + η - u)`
for every jump `u` at `i`, with sum of the costs `k.cost 0 y = v_p(y) + k.differentBound` at most
`stepCost`. Then for `H ≥ 3 κ + 2 stepCost` the cup product of the cocycles that `S` and `S'` attach
to `c` and `p ^ H • c'` is a continuous coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_gap (P : S.SidePairing S') {a κ η H W : ℕ}
    {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ} {stepCost : ℕ}
    (h_kill_tateDual : ∀ i : k.Letter, P.tateDualSide.KillsCokernel i κ a)
    (h_kill : ∀ i : k.Letter, S.KillsCokernel i κ a)
    (h_kill' : ∀ i : k.Letter, S'.KillsCokernel i κ a)
    (h_window : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (S.jumpSet i))
    (h_window' : ∀ i : k.Letter, FitsWindows η (ε i) (b i) W (S'.jumpSet i))
    (h_gap : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, u ∉ Ico (-a : ℤ) 0)
    (h_gap' : ∀ i : k.Letter, ∀ u ∈ S'.jumpSet i, u ∉ Ico (-a : ℤ) 0)
    (steps : k.Letter → ℤˣ → Finset ℤ)
    (h_steps : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, Ico (-u - a) (a + η - u) ⊆ steps i (-ε i))
    (h_steps' : ∀ i : k.Letter, ∀ u ∈ S'.jumpSet i, Ico (-u - a) (a + η - u) ⊆ steps i (ε i))
    (h_cost : ∀ (i : k.Letter) (σ : ℤˣ), ∑ y ∈ steps i σ, k.cost 0 y ≤ stepCost)
    (hH : 3 * κ + 2 * stepCost ≤ H)
    (c : S.paramLattice.Carrier) (c' : S'.paramLattice.Carrier) :
      P.IsScaledCupCoboundary H c c' := by
  -- Both sides have deep points without pole at every letter. At each letter the side whose far
  -- window is negative has jumps at most `η`; it provides a stop, a point at which it rests while
  -- the other side moves by Frobenius.
  choose x hx_no_pole using fun i ↦
    pointsOver_nonempty_of_gap (h_kill i) (h_gap i) (h_steps i) (h_cost i (-ε i)) c
  choose x' hx'_no_pole using fun i ↦
    pointsOver_nonempty_of_gap (h_kill' i) (h_gap' i) (h_steps' i) (h_cost i (ε i)) c'
  have hx (i : Letter) := mem_pointsOver_of_no_pole η (hx_no_pole i)
  have hx' (i : Letter) := mem_pointsOver_of_no_pole η (hx'_no_pole i)
  refine P.isScaledCupCoboundary_of_stops_at_all_letters x x' h_kill_tateDual
    (fun i ↦ mem_standardPoints_of_plainDepth (hx i))
    (fun i ↦ mem_standardPoints_of_plainDepth (hx' i)) (fun i ↦ ?_) (by omega)
  obtain Pε | Pε := units_eq_one_or (ε i)
  · have h_down : ∀ u ∈ S.jumpSet i, u ≤ η :=
      jump_le_of_fitsWindows (h_window i) (.inl (neg_inj.2 Pε))
    have h_up : ∀ u ∈ S'.jumpSet i, -η ≤ u := neg_le_jump_of_fitsWindows (h_window' i) (.inl Pε)
    exact .inl (P.exists_mem_stopPoints_isSafeMoveSnd one_pos (h_kill_tateDual i)
      (forall_mem_U_stepBack_of_lt_one h_down)
      (forall_mem_U_stepBack_of_lt_one h_up) (hx i) (hx' i) (hx'_no_pole (i.stepBack 1)))
  · have h_down : ∀ u ∈ S'.jumpSet i, u ≤ η := jump_le_of_fitsWindows (h_window' i) (.inl Pε)
    have h_up : ∀ u ∈ S.jumpSet i, -η ≤ u :=
      neg_le_jump_of_fitsWindows (h_window i) (.inl (neg_eq_iff_eq_neg.2 Pε))
    exact .inr (P.exists_mem_stopPoints_isSafeMoveFst one_pos (h_kill_tateDual i)
      (forall_mem_U_stepBack_of_lt_one h_down)
      (forall_mem_U_stepBack_of_lt_one h_up) (hx' i) (hx i) (hx_no_pole (i.stepBack 1)))

/-- Free steps. Let the Kummer chart be unramified, let `p` divide no nonzero integer within `n` of
`0`, `β` or `-β`, and let the side `S` have a point over `p ^ κ • c` at the letter `i` with orders
`lo` and depth `o`: an element of the extension over that constant whose values at each level `l`
and jump `u ∈ S.jumpSet (i.stepBack l)` have order at least `lo l u`, and whose differences with its
translates by the group of the chart have order at least `o l u`. If all steps `y` with
`o l u ≤ y < o' l u` are at the level `0` and within `n` of `0`, `β` or `-β`, then `S` has a point
over the same `p ^ κ • c` with depth `o'` and any orders `lo' ≤ improvedOrders lo o'`. -/
lemma pointsOver_nonempty_of_near_steps {κ : ℕ} {i : k.Letter} {c : S.paramLattice.Carrier}
    {lo lo' o o' : ℕ → ℤ → ℤ} {n : ℕ} {β : ℤ} (hk : k.IsUnramified)
    (hβ_gap : NoMultipleNear p n β) (h_point : (S.pointsOver c i κ lo o).Nonempty)
    (h_steps : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), ∀ y : ℤ, o l u ≤ y → y < o' l u →
      l = 0 ∧ y ∈ twoWindows n β ∪ twoWindows n (-β))
    (h_exponent : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), lo' l u ≤ improvedOrders lo o' l u) :
    (S.pointsOver c i κ lo' o').Nonempty := by
  obtain ⟨-, -, h_free : k.differentBound = 0⟩ := hk
  have h_cost : ∑ y ∈ twoWindows n β ∪ twoWindows n (-β), k.cost 0 y ≤ 0 := by
    rw [sum_cost_eq_card_mul hβ_gap (fun _ hy ↦ hy), h_free, Nat.mul_zero]
  obtain ⟨y, hy⟩ := pointsOver_nonempty_of_steps_level_zero h_point h_steps h_cost
  exact ⟨y, mem_pointsOver_of_exponent_le hy h_exponent⟩

/-- Let the chart be unramified (`E = z + p`), let `p ^ κ * E ^ a` kill the cokernel of the side
`S` at the letter `i` (it lifts each constant at `i` to the extension with standard orders), and let
the jumps, the elements of `S.jumpSet i`, lie in `[-η, η]` or in `σ • [β, β + W]`. Let `a ≤ t`, and
let `p` divide no nonzero integer within `n ≥ a + t + max η W` of `0` or `± β`. Then `S` has a point
over `p ^ κ • c` at `i` with a pole of order at most `t` (its orders `raisedOrdersAtZero (-t)` are
`-t - u` at the level `0` on the line of a jump `u`) and of depth `plainDepth a t 1 0`, which is
`a + t - u` at the level `0` and `-u` at the levels above. -/
lemma pointsOver_nonempty_of_fitsWindows {a κ η W t n β : ℕ} {σ : ℤˣ} {i : k.Letter}
    (hk : k.IsUnramified) (h_kill : S.KillsCokernel i κ a) (hβ_gap : NoMultipleNear p n β)
    (h_window : FitsWindows η σ β W (S.jumpSet i)) (hat : a ≤ t) (hn : a + t + max η W ≤ n)
    (c : S.paramLattice.Carrier) : (S.pointsOver c i κ (raisedOrdersAtZero (-t))
      (plainDepth a t 1 0)).Nonempty := by
  refine pointsOver_nonempty_of_near_steps hk hβ_gap (pointsOver_nonempty_of_killsCokernel h_kill c)
    (steps_at_level_zero ?_) ?_
  · intro u hu y hy
    rw [mem_Ico] at hy
    have hu_window := low_or_far_of_fitsWindows h_window hu
    exact mem_twoWindows_union_iff.2 (by omega)
  · intro l u _
    dsimp only [improvedOrders, raisedOrdersAtZero, plainDepth, standardDepth]
    split_ifs <;> omega

/-- Let the chart be unramified, let all jumps of the side `S` lie in `[-η, 0]`, and let `p` divide
no nonzero integer within `n ≥ a + t + η` of `0` or `± β`. Then at every letter `i` the side `S` has
a point without pole over the constant `S.constantAt i c` of `c`: on the line of each jump `u` its
orders are `-u` at every level. Its depth, the orders of its differences with its translates by the
group of the chart, is `plainDepth a t 1 0`: this is `a + t - u` at the level `0` and `-u` at the
levels above. -/
lemma pointsOver_nonempty_of_jumps_nonpos {a η t n : ℕ} {β : ℤ} (hk : k.IsUnramified)
    (hβ_gap : NoMultipleNear p n β) (hn : a + t + η ≤ n)
    (h_nonpos : ∀ j : k.Letter, S.jumpSet j ⊆ Finset.Icc (-η : ℤ) 0) (c : S.paramLattice.Carrier)
      (i : k.Letter) :
    (S.pointsOver c i 0 (raisedOrdersAtZero 0) (plainDepth a t 1 0)).Nonempty := by
  -- As the jumps are at most `0`, the element `1 = p ^ 0 * E ^ 0` kills the cokernel.
  have h_kill : S.KillsCokernel i 0 0 := killsCokernel_zero_zero_of_small_jumps (ω := 0)
    (fun j u hu ↦ (mem_Icc.1 (h_nonpos j hu)).2) (Nat.zero_le _) i
  -- With no pole, apply the gap lemma with pole order zero and total depth `a + t`.
  have h_depth : plainDepth 0 (a + t) 1 0 = plainDepth a t 1 0 := by
    funext l u
    cases l <;> simp [plainDepth, standardDepth]
    omega
  rw [← h_depth]
  refine pointsOver_nonempty_of_gap (stepCost := 0) h_kill (by simp)
    (steps := twoWindows n β ∪ twoWindows n (-β)) ?_ ?_ c
  · intro u hu y hy
    have := mem_Icc.1 (h_nonpos i hu)
    have := mem_Ico.1 hy
    exact mem_twoWindows_union_iff.2 (.inl (by omega))
  · exact sum_nonpos fun y hy ↦ cost_le_of_isUnramified hk (hβ_gap.eq_zero_of_dvd hy)

/-- On an unramified chart let the jumps `u` of the side `S'` lie in `[-η, 0]`, and let `x₀'` be a
point over `c'` at the letter `i.stepBack 1` before `i`, without pole and of depth `a + t - u` at
the level `0`, where `η ≤ t`. Let `p` divide no nonzero integer within `n ≥ a + t + η` of `0` or
`± β`. Then `S'` has a point over `c'` at `i` that can serve as a stop, that is, rest while the
other side of a pairing moves by Frobenius: its orders `stopOrders t 1` are `max 0 (-u - t)` at the
level `0` and `-u` above, and its depth is `a + t - u`, `t - u` and `-u` at the level `0`, the level
`1` and above. -/
lemma pointsOver_stopOrders_nonempty {a η : ℕ} {i : k.Letter} {c' : S'.paramLattice.Carrier}
  {t n : ℕ}
    {β : ℤ} {x₀' : S'.extensionLattice.Ambient} (hk : k.IsUnramified)
      (hβ_gap : NoMultipleNear p n β)
    (hn : a + t + η ≤ n) (hηt : η ≤ t) (h_nonpos : ∀ j : k.Letter,
      S'.jumpSet j ⊆ Finset.Icc (-η : ℤ) 0)
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack 1) 0 (raisedOrdersAtZero 0) (plainDepth a t 1 0)) :
    (S'.pointsOver c' i 0 (stopOrders t 1) (plainDepth a t 1 t)).Nonempty := by
  -- Frobenius shifts orders and depth by one level (`shiftedOrders`), which supplies the depth at
  -- the level `1`; the depth at the level `0` is then raised from `1`.
  have h_frob : FrobGroup.φ ^ 1 • x₀' ∈ S'.pointsOver c' i 0
      (shiftedOrders 1 0 (raisedOrdersAtZero 0)) (shiftedOrders 1 1 (plainDepth a t 1 0)) :=
    phi_pow_smul_mem_pointsOver hx₀'
  have h_steps : ∀ l : ℕ, ∀ u ∈ S'.jumpSet (i.stepBack l), ∀ y : ℤ,
      shiftedOrders 1 1 (plainDepth a t 1 0) l u ≤ y → y < plainDepth a t 1 t l u →
      l = 0 ∧ y ∈ twoWindows n β ∪ twoWindows n (-β) :=
    fun l u hu y hy_ge hy_lt ↦ by
      have hu' := mem_Icc.1 (h_nonpos _ hu)
      dsimp only [shiftedOrders, plainDepth, standardDepth] at hy_ge hy_lt
      refine ⟨by split_ifs at hy_ge hy_lt <;> omega, mem_twoWindows_union_iff.2 ?_⟩
      split_ifs at hy_ge hy_lt <;> omega
  have h_exponent : ∀ l : ℕ, ∀ u ∈ S'.jumpSet (i.stepBack l), stopOrders t 1 l u ≤
      improvedOrders (shiftedOrders 1 0 (raisedOrdersAtZero 0)) (plainDepth a t 1 t) l u :=
    fun l u hu ↦ by
      have hu' := mem_Icc.1 (h_nonpos _ hu)
      dsimp only [stopOrders, stdOrders, improvedOrders, shiftedOrders, raisedOrdersAtZero,
        plainDepth, standardDepth]
      split_ifs <;> omega
  exact pointsOver_nonempty_of_near_steps hk hβ_gap ⟨_, h_frob⟩ h_steps h_exponent

/-- Let the chart be unramified, let `P` be a pairing of the lattices of the sides `S` and `S'`, and
`P.tateDualSide` the side on the Tate dual of their tensor product that carries the pairing. At
every letter `i` let `p ^ κ * E ^ a`, with `E = z + p` the distinguished element of the chart, kill
the cokernels of `S` and of `P.tateDualSide`, and let `p` divide no nonzero integer within
`n ≥ a + max a η + max η W` of `0` or `± b i`. Let the jumps of `S` lie in `[-η, η]` or in
`-ε i • [b i, b i + W]` for a sign `ε i = ±1`, and let the jumps of `S'` lie in `[-η, 0]`. Then for
`H ≥ 2 κ` the cup product of the cocycles that `S` and `S'` attach to `c` and `p ^ H • c'` is a
continuous coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_jumps_nonpos (P : S.SidePairing S') {a κ η H W n : ℕ}
    {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ} (hk : k.IsUnramified)
    (h_kill_tateDual : ∀ i : k.Letter, P.tateDualSide.KillsCokernel i κ a)
    (h_kill : ∀ i : k.Letter, S.KillsCokernel i κ a)
    (hb_gap : ∀ i : k.Letter, NoMultipleNear p n (b i))
    (hn : a + max a η + max η W ≤ n)
    (h_window : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (S.jumpSet i))
    (h_nonpos : ∀ i : k.Letter, S'.jumpSet i ⊆ Finset.Icc (-η : ℤ) 0) (hH : 2 * κ ≤ H)
    (c : S.paramLattice.Carrier) (c' : S'.paramLattice.Carrier) :
      P.IsScaledCupCoboundary H c c' := by
  -- Use the bound `t = max a η` for the poles and the low jumps. The jumps of `S'` lie in `[-t, t]`
  -- and its points have no pole. Where the far window of `S` is negative, `S` provides the stop
  -- (the point at rest while the other side moves by Frobenius); elsewhere `S'` does.
  let t := max a η
  have hat : a ≤ t := le_max_left _ _
  have hηt : η ≤ t := le_max_right _ _
  have h_radius : a + t + η ≤ n := (Nat.add_le_add_left (le_max_left η W) _).trans hn
  choose x hx using fun i ↦
    pointsOver_nonempty_of_fitsWindows hk (h_kill i) (hb_gap i) (h_window i) hat hn c
  choose x' hx'_no_pole using fun i ↦
    pointsOver_nonempty_of_jumps_nonpos hk (hb_gap i) h_radius h_nonpos c' i
  have hx' (i : Letter) := mem_pointsOver_of_no_pole t (hx'_no_pole i)
  refine P.isScaledCupCoboundary_of_stops_at_all_letters x x' h_kill_tateDual
    (fun i ↦ mem_standardPoints_of_plainDepth (hx i))
    (fun i ↦ mem_standardPoints_of_plainDepth (hx' i)) (fun i ↦ ?_) (by omega)
  obtain Pε | Pε := units_eq_one_or (ε i)
  · have h_down : ∀ u ∈ S.jumpSet i, u ≤ t :=
      fun u hu ↦ (jump_le_of_fitsWindows (h_window i) (.inl (neg_inj.2 Pε)) u hu).trans (by omega)
    have h_up : ∀ u ∈ S'.jumpSet i, -t ≤ u := fun u hu ↦ by
      have := (mem_Icc.1 (h_nonpos i hu)).1
      omega
    exact .inl (P.exists_mem_stopPoints_isSafeMoveSnd one_pos (h_kill_tateDual i)
      (forall_mem_U_stepBack_of_lt_one h_down)
      (forall_mem_U_stepBack_of_lt_one h_up) (hx i) (hx' i) (hx'_no_pole (i.stepBack 1)))
  · have h_up : ∀ u ∈ S.jumpSet i, -t ≤ u :=
      fun u hu ↦ le_trans (by omega)
        (neg_le_jump_of_fitsWindows (h_window i) (.inl (neg_eq_iff_eq_neg.2 Pε)) u hu)
    obtain ⟨q', hq'⟩ : (S'.pointsOver c' i 0 (stopOrders t 1) (plainDepth a t 1 t)).Nonempty :=
      pointsOver_stopOrders_nonempty hk (hb_gap i) h_radius hηt h_nonpos
        (hx'_no_pole (i.stepBack 1))
    have h_safe : P.IsSafeMoveFst κ (FrobGroup.φ ^ 1 • x (i.stepBack 1) - x i) q' :=
      P.isSafeMoveFst_of_neg_le_jumps one_pos (h_kill_tateDual i)
        (forall_mem_U_stepBack_of_lt_one h_up)
        (hx i)
        (hx (i.stepBack 1)) hq'
    exact .inr ⟨q', mem_stopPoints_of_mem_pointsOver hq', h_safe⟩

/-- Let `P` be a pairing of the lattices of the sides `S` and `S'`, and `P.tateDualSide` the side on
the Tate dual of their tensor product that carries the pairing. At every letter `i` let
`p ^ κ * E ^ a`, with `E` the distinguished element of the chart, kill the cokernels of `S`, `S'`
and `P.tateDualSide`, let `p` divide no nonzero integer within `n ≥ a + max a η + max η W` of `0` or
`± b i`, and let the jumps of `S` and `S'` lie in `[-η, η]` or in the opposite far windows
`∓ε i • [b i, b i + W]`, where `ε i = ±1`. Suppose that no jump lies in `[-a, 0)`, or that the chart
is unramified and the jumps of `S'` lie in `[-η, 0]`. Then for
`H ≥ 3 κ + 2 (4 a + 4 η + W) k.differentBound` the cup product of the cocycles of `c` and
`p ^ H • c'` is a continuous coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_killsCokernel (P : S.SidePairing S') {a κ η H W n : ℕ}
    {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ}
    (h_kill_tateDual : ∀ i : k.Letter, P.tateDualSide.KillsCokernel i κ a)
    (h_kill : ∀ i : k.Letter, S.KillsCokernel i κ a)
    (h_kill' : ∀ i : k.Letter, S'.KillsCokernel i κ a)
    (hb_gap : ∀ i : k.Letter, NoMultipleNear p n (b i))
    (hn : a + max a η + max η W ≤ n)
    (h_window : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (S.jumpSet i))
    (h_window' : ∀ i : k.Letter, FitsWindows η (ε i) (b i) W (S'.jumpSet i))
    (h_gap_or_nonpos :
      -- no jump lies in `[-a, 0)`
      (∀ (i : k.Letter) (u : ℤ), u ∈ S.jumpSet i ∨ u ∈ S'.jumpSet i → u ∉ Ico (-a : ℤ) 0) ∨
      -- unramified chart, and the jumps of `S'` lie in `[-η, 0]`
      k.IsUnramified ∧ ∀ i : k.Letter, S'.jumpSet i ⊆ Finset.Icc (-η : ℤ) 0)
    (hH : 3 * κ + 2 * ((4 * a + 4 * η + W) * k.differentBound) ≤ H)
    (c : S.paramLattice.Carrier) (c' : S'.paramLattice.Carrier) :
      P.IsScaledCupCoboundary H c c' := by
  obtain h_gap | ⟨hk, h_nonpos⟩ := h_gap_or_nonpos
  · -- Each side has the low interval and only one of the two far intervals.
    let far (β : ℤ) (σ : ℤˣ) := if (σ : ℤ) = 1 then -β - W else β
    let steps (β : ℤ) (σ : ℤˣ) := Ico (-(a : ℤ) - η) (a + 2 * (η : ℤ)) ∪
      Ico (far β σ - a) (far β σ + W + a + η)
    have h_steps {σ : ℤˣ} {β : ℕ} {U : Finset ℤ} (hU : FitsWindows η σ β W U) :
        ∀ u ∈ U, Ico (-u - a) (a + η - u) ⊆ steps β σ := by
      intro u hu y hy
      have h := hU u hu
      simp only [steps, mem_union, mem_Ico] at hy ⊢
      by_cases hs : (σ : ℤ) = 1 <;> simp only [far, hs, ite_true, ite_false] <;> omega
    have h_cost (i : k.Letter) (σ : ℤˣ) : ∑ y ∈ steps (b i) σ, k.cost 0 y ≤
        (4 * a + 4 * η + W) * k.differentBound := by
      rw [sum_cost_eq_card_mul (hb_gap i) (by
        intro y hy
        rw [mem_twoWindows_union_iff]
        simp only [steps, mem_union, mem_Ico] at hy
        by_cases hs : (σ : ℤ) = 1 <;> simp only [far, hs, ite_true, ite_false] at hy <;>
          omega : steps (b i) σ ⊆ _)]
      apply Nat.mul_le_mul_right
      dsimp only [steps]
      grw [card_union_le]
      simp only [Int.card_Ico]
      omega
    exact P.isScaledCupCoboundary_of_gap h_kill_tateDual h_kill h_kill' h_window h_window'
      (fun i u hu ↦ h_gap i u (.inl hu)) (fun i u hu ↦ h_gap i u (.inr hu))
      (fun i ↦ steps (b i)) (fun i ↦ h_steps (h_window i)) (fun i ↦ h_steps (h_window' i))
      h_cost hH c c'
  · exact P.isScaledCupCoboundary_of_jumps_nonpos hk h_kill_tateDual h_kill hb_gap hn h_window h_nonpos
      (by omega) c c'

end New.Lift.KummerChart.PairingSide
