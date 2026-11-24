module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

theorem galois_twist_preserves_siegel_bound (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hW : WickOperatorVanishing) : AdmissibilitySecond := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' w0 m ι _ u P hP f
  unfold FB.nabVal
  set a : Fin 2 → Pt k 1 d := ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] with hadef
  set q := ev (n := 1) a (h' - h) with hqdef
  have hbi := hG R d O k B h h' hh hh'
  obtain ⟨hq0, hq1, hq2⟩ := hQ R d O k B (h' - h) hbi w0
  have hac : ∀ j i, constantCoeff (a j i) = 0 := by
    intro j i
    fin_cases j
    · simp [hadef, pt]
    · show constantCoeff (ev (n := 1) ![pt k d 0] (B.actK k w0 i)) = 0
      rw [hE k d 1 1 ![pt k d 0] _ (fun j i => by fin_cases j; simp [pt])]
      simp only [FB.actK]
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, B.A.const, map_zero]
  have hs : HasSubst (fun p : Fin 2 × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => hac p.1 p.2
  have hL' : B.hL k h' w0 = B.hL k h w0 + q := by
    simp only [FB.hL, hqdef, ev]
    rw [subst_sub hs]
    ring
  have hh0 : constantCoeff h = 0 := by
    have h1 := hE k d 2 1 ![0, pt k d 0] h (fun j i => by fin_cases j <;> simp [pt])
    rw [hh.ax0] at h1
    simpa using h1.symm
  have hL0 : constantCoeff (B.hL k h w0) = 0 := by
    simp only [FB.hL]
    rw [hE k d 2 1 _ h hac, hh0]
  have hexp : FB.expS k ((m : k) • B.hL k h' w0) =
      FB.expS k ((m : k) • B.hL k h w0) * FB.expS k ((m : k) • q) := by
    rw [hL', smul_add]
    exact hA k 1 d _ _ (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hL0, mul_zero])
      (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq0, mul_zero])
  rw [hexp, ← mul_assoc]
  symm
  exact hW k d (B.FK k) ι u
    (fun l l' => dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
    P q (fun l l' => add_comm _ _) hq0 (fun l => hq1 (u l)) (fun l l' => hq2 (u l) (u l')) hP (m : k)
    (f * FB.expS k ((m : k) • B.hL k h w0))

end ReciprocityTheory.ChartRestriction.G.TB.G2
