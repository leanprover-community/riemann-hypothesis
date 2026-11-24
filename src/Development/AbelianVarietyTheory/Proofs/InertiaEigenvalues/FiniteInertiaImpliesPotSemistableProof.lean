module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePeriodUnramifiedRepStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOverFinExtOfFiniteInertiaImageStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unrStep_holds : UnrStep := by
  intro l _ P AI T n _ _ K r ρ hρ hfin
  obtain ⟨K', hK, hI, hc⟩ := GlobalTheory.T.unramified_over_finExt_of_finite_inertia_image l n K r ρ hρ hfin
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  let ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l) := ρ.comp ι
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hρ' : IsRat r ρ' :=
    { pos := hρ.pos
      le := fun c hc => hK (hρ.le c hc)
      rat := fun g i j => hρ.rat (ι g) i j
      cont := fun i j => (hρ.cont i j).comp hι }
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_crystalline_period_unramified_rep l P AI T n K' r ρ' hρ' (fun g hg => hI g hg) (fun g i j => hc g i j)
  refine ⟨K', hK, Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q, fun g => ?_⟩
  have h1 : ((Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q : GL n (Bst P)) :
      Matrix n n (Bst P)) = (Q : Matrix n n P.R.B).map Polynomial.C := rfl
  have h2 : ((Q : Matrix n n P.R.B).map Polynomial.C).map (actSt P (g : GQ l)) =
      ((Q : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (Polynomial.C : P.R.B →+* Bst P) := by
    rw [Matrix.map_map, Matrix.map_map]
    congr 1
    funext b
    exact actSt_C P _ b
  have h3 : (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) =
      ((ρ' g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (Polynomial.C : P.R.B →+* Bst P) := by
    rw [Matrix.map_map]
    rfl
  rw [h1, h2, h3, ← Matrix.map_mul, hQ g]

end GlobalTheory.PMon

end
