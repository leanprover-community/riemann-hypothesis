module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory

theorem absoluteGalois_fixes_unramified_in_crystalline {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (g : ↥(GK K))
    (a : ↥(K0 K)) : P.actQ (g : GQ l) (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.B a := by
  have hfix : (g : GQ l) ((a : Om l)) = (a : Om l) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 (a : Om l) a.2.1
  exact P.actQ_Kur (g : GQ l) (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a)
    (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a) hfix

theorem ltChar_hom : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : P.R.B), IsUnit x → (∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x) → ∃ c : ↥(GK K) →* (↥(K0 K))ˣ, ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x := by
  intro l _ P K x hx h
  rcases subsingleton_or_nontrivial P.R.B with hB | hB
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  · have hinj : Function.Injective (algebraMap ↥(K0 K) P.R.B) := (algebraMap ↥(K0 K) P.R.B).injective
    have hcan : ∀ a b : ↥(K0 K), algebraMap ↥(K0 K) P.R.B a * x = algebraMap ↥(K0 K) P.R.B b * x → a = b :=
      fun a b e => hinj (hx.mul_left_injective e)
    let f : ↥(GK K) → ↥(K0 K) := fun g : ↥(GK K) => Classical.choose (h g)
    have hf : ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B (f g) * x :=
      fun g => Classical.choose_spec (h g)
    let F : ↥(GK K) →* ↥(K0 K) :=
      { toFun := f
        map_one' := by
          apply hcan
          rw [← hf, map_one, one_mul, OneMemClass.coe_one, map_one, AlgEquiv.one_apply]
        map_mul' := by
          intro g g'
          apply hcan
          rw [← hf]
          have e1 : P.actQ ((g * g' : ↥(GK K)) : GQ l) x = P.actQ (g : GQ l) (P.actQ (g' : GQ l) x) := by
            rw [Subgroup.coe_mul, map_mul, AlgEquiv.mul_apply]
          rw [e1, hf g', map_mul, absoluteGalois_fixes_unramified_in_crystalline, hf g, map_mul]
          ring }
    refine ⟨F.toHomUnits, fun g => ?_⟩
    rw [MonoidHom.coe_toHomUnits]
    exact hf g

end GlobalTheory
