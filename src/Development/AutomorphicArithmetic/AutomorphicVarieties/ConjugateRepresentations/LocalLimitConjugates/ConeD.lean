module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PoinPt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneD :
    UpperTheory.V.Cj.H.ConeD := by
  intro V F _ _ _ _ _ _ Y hYo hYc p hp q w hw
  have hseg : ∀ x ∈ Y, ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (x - p) ∈ Y := by
    intro x hx t ht
    have h := hYc hp hx (sub_nonneg.2 ht.2) ht.1 (by ring)
    convert h using 1
    rw [smul_sub, sub_smul, one_smul]
    abel
  let g : V × ℝ → V := fun z => p + z.2 • (z.1 - p)
  have hg : ContDiff ℝ ⊤ g := by
    exact contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))
  let W : Set (V × ℝ) := g ⁻¹' Y
  have hW : IsOpen W := hYo.preimage hg.continuous
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p + z.2 • (z.1 - p))).curryLeft (z.1 - p)
  have hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ W := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => w (g z)) W :=
      hw.comp (hg.of_le le_top).contDiffOn (fun z hz => hz)
    let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
    have hfst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.1 - p) :=
      contDiff_fst.sub contDiff_const
    have h2 := (L.contDiff.comp_contDiffOn h1).clm_apply (hfst.contDiffOn (s := W))
    have hsnd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.2 ^ q) :=
      contDiff_snd.pow q
    exact hsnd.contDiffOn.smul h2
  have hsub : Y ×ˢ Set.Icc (0:ℝ) 1 ⊆ W := fun z hz => hseg z.1 hz.1 z.2 hz.2
  refine ⟨UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y W Φ hYo hW hsub hΦ, ?_⟩
  intro hcl x hx
  have hd := UpperTheory.V.Lit.Dr.paramDeriv V (V [⋀^Fin q]→L[ℝ] F) x W Φ hW (fun t ht => hseg x hx t ht) hΦ
  have hI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V F (n := q)
  have hint : IntervalIntegrable (fun t => fderiv ℝ (fun y => Φ (y, t)) x) MeasureTheory.volume 0 1 :=
    (hI ▸ hd.1).intervalIntegrable
  have hcont' : ContinuousOn (fun t => A (fderiv ℝ (fun y => Φ (y, t)) x)) (Set.uIcc 0 1) :=
    hI ▸ (A.continuous.comp_continuousOn hd.1)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p + r • (x - p))) (A (fderiv ℝ (fun y => Φ (y, t)) x)) t := by
    intro t ht
    rw [hI] at ht
    have hm := hseg x hx t ht
    have hdiff : DifferentiableAt ℝ w (p + t • (x - p)) :=
      (hw.contDiffAt (hYo.mem_nhds hm)).differentiableAt (by simp)
    exact UpperTheory.V.Lit.Dr.poinPt V F q w p x t hdiff (hcl _ hm)
  have hfd : fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x = ∫ t in (0:ℝ)..1, fderiv ℝ (fun y => Φ (y, t)) x :=
    hd.2.fderiv
  have key : extDeriv (UpperTheory.V.Cj.H.coneOp p w) x = A (fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x) := rfl
  rw [key, hfd, ← A.intervalIntegral_comp_comm hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont'.intervalIntegrable)]
  simp
