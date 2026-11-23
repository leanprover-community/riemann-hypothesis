module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.neglAt_pf :
    UpperTheory.Gal.Gen.GlobOp → UpperTheory.Gal.Gen.Small → UpperTheory.Gal.Gen.NeglAt := by
  intro hG hS E _ _ _ a K w₀ w hs hap hyp Φ hΦ δ hδ
  obtain ⟨C, hC⟩ := hG E a K w hs hyp
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨p, hp, hp1, hI⟩ := hS a Φ hΦ (δ / (|C| + 1)) (div_pos hδ hC1)
  obtain ⟨h, hloc, hsep, hnorm, hop⟩ := hC p hp
  refine ⟨h, ?_, hsep, ?_, ?_⟩
  · intro g hg
    have hm := (GlobalTheory.Cong.LevelExt.mem_locU_iff g).1 (hloc g hg)
    refine ⟨hm.1, fun u hu => hm.2 u ?_⟩
    have e : u.under (𝓞 (maximalRealSubfield E)) = w₀.under (𝓞 (maximalRealSubfield E)) :=
      Classical.byContradiction hu
    intro e'
    exact hap (e'.symm.trans e)
  · have hI0 : 0 ≤ ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    calc ∑ g ∈ h.support, ‖h g‖ ^ 2
        ≤ C * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 := hnorm
      _ ≤ |C| * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hI0
      _ ≤ |C| * (δ / (|C| + 1)) := mul_le_mul_of_nonneg_left hI (abs_nonneg C)
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ hC1]
          nlinarith [abs_nonneg C]
  · intro U hU hB φ hφ hfix
    have hB' : ¬ GenAt w Φ U := hB
    unfold GenAt at hB'
    push_neg at hB'
    obtain ⟨z, hz, h0⟩ := hB'
    rw [hop U hU z hz φ hφ hfix, hp1 z h0, one_smul]
