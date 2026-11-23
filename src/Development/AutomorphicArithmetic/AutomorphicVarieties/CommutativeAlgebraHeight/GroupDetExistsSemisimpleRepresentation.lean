module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DKerSs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsSemisimpleRepOfDetLawOfIsAlgClosed
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.groupDet_exists_semisimple_representation :
    ∀ {n : ℕ} {k G : Type} [Field k] [IsAlgClosed k] [Group G] (D : GDet n k G), ∃ ρ : G →* Matrix (Fin n) (Fin n) k, IsSemisimpleRing (GDet.repAlg ρ k).range ∧ GDet.ofRep ρ = D ∧ ∀ y, D.Kills y ↔ GDet.repAlg ρ k y = 0 := by
  intro n k G _ _ _ D
  obtain ⟨r, hss, hD⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed D.toDet
  let ρ : G →* Matrix (Fin n) (Fin n) k := (r : MonoidAlgebra k G →* Matrix (Fin n) (Fin n) k).comp
    (MonoidAlgebra.of k G)
  have hr : GDet.repAlg ρ k = r := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [GDet.repAlg, ρ, MonoidAlgebra.lift_single]
    · ext
  refine ⟨ρ, hr ▸ hss, ?_, fun y => ?_⟩
  · have hrep : (GDet.ofRep ρ).toDet = Det.ofRep (Fintype.card_fin n) (GDet.repAlg ρ k) := by
      refine Det.ext' fun S _ _ x => ?_
      change (GDet.repAlg ρ S (ofT k G S x)).det = (Det.repS (GDet.repAlg ρ k) S x).det
      congr 1
      induction x with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul s y =>
        rw [ofT_tmul, Det.repS_tmul, map_smul]
        congr 1
        induction y using MonoidAlgebra.induction_linear with
        | zero => ext i j; simp
        | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
        | single g a => ext i j; simp [GDet.repAlg]
    rw [← GDet.ofDet_toDet (GDet.ofRep ρ), hrep, hr, hD, GDet.ofDet_toDet]
  · have hval (S : Type) [CommRing S] [Algebra k S] (h : S ⊗[k] MonoidAlgebra k G) :
        D.toDet.D S (1 + h * (1 ⊗ₜ y)) =
          D.D S (1 + ofT k G S h * MonoidAlgebra.mapRingHom G (algebraMap k S) y) := by
      change D.D S (ofT k G S (1 + h * (1 ⊗ₜ y))) = _
      rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
    have hkills : D.toDet.Kills y ↔ D.Kills y := by
      constructor
      · intro hk S _ _ h
        have hh := hk S (toT k G S h)
        rwa [hval, ofT_toT] at hh
      · intro hk S _ _ h
        rw [hval]
        exact hk S _
    rw [← hkills, ← (d_ker D.toDet y).1, ← hD, d_ker_ss _ r hss, hr]
