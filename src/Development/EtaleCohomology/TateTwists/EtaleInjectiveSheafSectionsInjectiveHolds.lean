module

public import Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle
public import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.AB
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwResSecInj

theorem sigma_map_mono (R : Type) [CommRing R] (ι : Type) {X Y : ModuleCat.{1} (ULift.{1} R)} (f : X ⟶ Y) [Mono f] :
    Mono (Limits.Sigma.map (fun (_ : ι) => f)) := by
  let α : Discrete.functor (fun (_ : ι) => X) ⟶ Discrete.functor (fun _ => Y) := Discrete.natTrans (fun _ => f)
  have : ∀ j, Mono (α.app j) := fun j => by
    change Mono f; infer_instance
  have h1 : Mono α := NatTrans.mono_of_mono_app _
  exact (colim : (Discrete ι ⥤ ModuleCat.{1} (ULift.{1} R)) ⥤ _).map_mono α

instance evLA_mono (R : Type) [CommRing R] (U : Scheme.{0}) :
    (evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    have hm : ∀ c, Mono (((evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).map f).app c) := by
      intro c
      rw [evaluationLeftAdjoint_map_app]
      have e : (Limits.Sigma.desc fun h => f ≫ Sigma.ι (fun _ => Y) h) = Limits.Sigma.map (fun (_ : op U ⟶ c) => f) := by
        ext; simp
      rw [e]; exact sigma_map_mono R _ f
    exact NatTrans.mono_of_mono_app _

end LateralTheory.EtaleFoundations.TwResSecInj

open LateralTheory.EtaleFoundations.TwResSecInj in
theorem LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  intro R _ M _ U
  have adj := (evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
  have hI := Injective.injective_of_adjoint adj M
  exact Module.injective_module_of_injective_object (inj := hI) _ _
