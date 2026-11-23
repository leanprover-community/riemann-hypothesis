module

public import Development.EtaleCohomology.EtaleSheaves.SimplicialPieceRelations
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.SimplicialPieceRelations SimplicialObject SimplicialObject.Augmented

namespace LateralTheory.E.SimplicialPieceDiscrete

variable (R : Type) [CommRing R]

def aug (X : PSh) : SimplicialObject.Augmented (Shv R) where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj X)
  right := (free R).obj X
  hom := { app := fun _ => 𝟙 _, naturality := by intros; (try simp); (try rfl) }

def augMap {X Y : PSh} (f : X ⟶ Y) : aug R X ⟶ aug R Y where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).map (disc.map f)
  right := (free R).map f
  w := by
    apply NatTrans.ext; funext n; exact (Category.comp_id _).trans (Category.id_comp _).symm

def ed (X : PSh) : ExtraDegeneracy (aug R X) where
  s' := 𝟙 _
  s := fun _ => 𝟙 _
  s'_comp_ε := by simp [aug] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s₀_comp_δ₁ := by simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ₀ := by intro n; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ := by intro n i; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_σ := by intro n i; simp [aug, SimplicialObject.σ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _

variable {R}

def hext {K L : ChainComplex (Shv R) ℕ} (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

def sIso (A : Shv R) := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat A 0 (0 : ℤ) (by simp)

theorem sIso_nat {A B : Shv R} (φ : A ⟶ B) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ (Shv R)).map φ) ComplexShape.embeddingDownNat ≫ (sIso B).hom =
      (sIso A).hom ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [sIso, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) (by simp),
    HomologicalComplex.single_map_f_self]

theorem disc0 : Disc0 := by
  intro R _ X Y f
  refine ⟨HomotopyCategory.isoOfHomotopyEquiv (hext (ed R X).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _),
    HomotopyCategory.isoOfHomotopyEquiv (hext (ed R Y).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _), ?_⟩
  have hn := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Shv R)).naturality (augMap R f)
  have key : (chains R).map (disc.map f) ≫ HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R Y)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj Y)).hom =
      HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj X)).hom ≫
        (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := by
    have h2 := congrArg (fun φ => HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) hn
    simp only [HomologicalComplex.extendMap_comp] at h2
    have h1 : HomologicalComplex.extendMap ((point ⋙ ChainComplex.single₀ (Shv R)).map (augMap R f)) ComplexShape.embeddingDownNat ≫
        (sIso ((free R).obj Y)).hom = (sIso ((free R).obj X)).hom ≫
          (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := sIso_nat ((free R).map f)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (sIso ((free R).obj Y)).hom) h2).trans
      ((Category.assoc _ _ _).trans (congrArg (HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ ·) h1)))
  have := congrArg (Qt R).map key
  simp only [Functor.map_comp] at this
  simp only [Iso.trans_hom, Category.assoc]
  exact this

theorem Piece_of : LateralTheory.E.TruncationPieces.Piece := LateralTheory.E.SimplicialPieceRelations.piece_of disc0

end LateralTheory.E.SimplicialPieceDiscrete
