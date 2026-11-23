module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KerOo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.OdComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.koszulThree_of_det :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A), T.ProL → T.Eig x al → K3 Λ.h k := by
  intro l _ L G0 T Λ n x k al hP hE
  intro z hz
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := by
    intro g
    ext i j
    simp [NP.ρX]
  have hzero : ∀ j, z (Λ.ta j) = 0 := by
    intro j
    have hc := Λ.comm j
    have h1 := hz.2.2.1 (Λ.ph j) (Λ.ta j)
    have h2 := hz.2.2.1 (Λ.ta j) (Λ.ph j)
    rw [hc] at h1
    simp only [hρ, map_inv, Λ.p_ta, Λ.p_ph, map_one, inv_one, one_mul, mul_one] at h1 h2
    rw [h2] at h1
    have h3 : z (Λ.ta j) = mat x.ρ (T.sg j) * z (Λ.ta j) * mat x.ρ (T.sg j)⁻¹ := by
      have := h1
      rw [add_comm (z (Λ.ta j))] at this
      exact add_left_cancel this
    have hPZ : mat x.ρ (T.sg j) * z (Λ.ta j) = z (Λ.ta j) * mat x.ρ (T.sg j) := by
      conv_rhs => rw [h3]
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    exact od_comm x.A n x.a (mat x.ρ (T.sg j)) (z (Λ.ta j)) (al j) (x.blk _) (hz.1 _)
      (hE j).1 (hE j).2 hPZ
  obtain ⟨y, hy⟩ := coc_ker l L Λ.G G0 Λ.h n x (Set.range Λ.ta) z
    (by rw [← Set.range_comp]; exact ker_oo l L G0 T Λ hP)
    (by
      rintro a ⟨j, rfl⟩
      exact ⟨Λ.p_ta j, hzero j⟩)
    hz
  have hzy : (fun g => y (Λ.h.p₀ g)) = z := funext hy
  have hy' : y ∈ SelZ G0.frame x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    rw [← Glob.Hom.sel_iff Λ.h, hzy]
    exact hz
  obtain ⟨s, c, hsc⟩ := k.gen y hy'
  refine ⟨s, c, ?_⟩
  have hb := (Glob.Hom.bd_iff Λ.h (x.ρX x.A) (Od x.A x.A n x.a) _).mpr hsc
  show _ ∈ Bd Λ.G.frame (fun g => x.ρX x.A (Λ.h.p₀ g)) (Od x.A x.A n x.a)
  convert hb using 1
  funext g
  simp [hy]
