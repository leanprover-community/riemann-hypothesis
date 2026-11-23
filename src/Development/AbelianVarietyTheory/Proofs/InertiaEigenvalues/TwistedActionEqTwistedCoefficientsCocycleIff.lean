module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem actTw_eq_twCoef_and_isCoc_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  intro G _ _ LL _ O _ _ V _ _ _ _ ρ L X _ _ χ
  have h1 : ∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul]
      rw [coefRep_tmul, twistRep_apply]
      simp [latRep, smul_tmul', MonoidHom.inv_apply]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  refine ⟨h1, fun z => ?_⟩
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨⟨hz, fun _ => Submodule.mem_top⟩, ?_⟩
    show (ReciprocityTheory.Def.d1 (twCoef (latRep L) χ X)) z = 0
    funext x
    change twCoef (latRep L) χ X x.1 (z x.2) - z (x.1 * x.2) + z x.1 = 0
    rw [hc, ← h1]; abel
  · rintro ⟨⟨hz, -⟩, hk⟩
    refine ⟨hz, fun g h => ?_⟩
    have e : twCoef (latRep L) χ X g (z h) - z (g * h) + z g = 0 := congrFun hk (g, h)
    rw [h1, ← sub_eq_zero, ← neg_eq_zero, ← e]; abel

end GlobalTheory
