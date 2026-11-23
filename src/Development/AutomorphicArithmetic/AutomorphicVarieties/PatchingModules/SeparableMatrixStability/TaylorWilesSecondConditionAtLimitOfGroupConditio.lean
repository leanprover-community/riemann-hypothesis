module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.LcOfAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.taylorWiles_second_condition_at_limit_of_group_condition :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x), T.B2 k → SecondSelmerSpanBoundAtAllLevels Λ.h k := by
  intro l _ L G0 T Λ n x k hB
  obtain ⟨C, hC⟩ := hB
  refine ⟨C, fun m z hz => ?_⟩
  obtain ⟨hfin, -, hn1, hn2, -, -⟩ := am_fin l G0.frame n x m k.g
  obtain ⟨⟨a1, a2, -⟩, ⟨b1, b2, -⟩, hlc, -⟩ := rho_hom l G0.frame n x k (x.Am m)
  obtain ⟨c1, c2⟩ := hlc hn1
  have E1 := t1 l L G0 T Λ n x.A (x.Am m) x.t (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m))
    (Ev x.A (x.Am m) n x.a) hn1 a1 a2 c1
  have E2 := t1 l L G0 T Λ n x.A (DD (x.Am m) k.g) x.t (k.ρ1 (x.Am m)) (k.w1 (x.Am m)) (k.wi1 (x.Am m))
    (W2 n x.A (x.Am m) k.g x.a) hn2 b1 b2 c2
  obtain ⟨N, ⟨⟨-, h1, -⟩, ⟨-, -, h2⟩⟩, h3⟩ := ((E1.and E2).and ((hC m).filter_mono Λ.U_le)).exists
  choose zN hzN hrel using fun i j => h1 (z i j) (hz i j)
  obtain ⟨c, hc, ΨN, hΨN, hΨ⟩ := h3 zN hzN
  obtain ⟨Ψ, hΨm, hr⟩ := h2 ΨN hΨN
  refine ⟨c, hc, Ψ, hΨm, fun j γ a b => ?_⟩
  obtain ⟨g, rfl⟩ := Λ.πo0_surj γ
  rw [← hr g, hΨ]
  simp only [hrel _ _ g]
