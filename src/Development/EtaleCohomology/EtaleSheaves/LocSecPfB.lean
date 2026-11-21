import Development.EtaleCohomology.EtaleSheaves.LeafLocPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPf

abbrev pt (R : Type) [CommRing R] (X : Scheme.{0}) : Cx R :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj X))

def LocSecA : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ CohomologyClass (pt R X) (res R F) n)

def LocSecB : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem LocSec_of (hA : LocSecA) (hB : LocSecB) : LateralTheory.E.LeafLocPf.LocSec := by
  intro _ R _ X F n
  obtain ⟨a⟩ := hA R X F n
  obtain ⟨b⟩ := hB R X F n
  exact ⟨a.trans b⟩

end LateralTheory.E.LocSecPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfA

variable (R : Type) [CommRing R]

def hEq (X : Scheme.{0}) : HomotopyEquiv ((chainsN R).obj (sch.obj X))
    ((ChainComplex.single₀ (Shv R)).obj ((free R).obj (yoneda.obj X))) :=
  ((SimplicialObject.Augmented.ExtraDegeneracy.const (yoneda.obj X)).map (free R)).homotopyEquiv

abbrev Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

def isoQ (X : Scheme.{0}) : (Q R).obj ((chains R).obj (sch.obj X)) ≅ (Q R).obj (LateralTheory.E.LocSecPf.pt R X) :=
  ((ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _).symm ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctor (Shv R)).mapIso (HomotopyCategory.isoOfHomotopyEquiv (hEq R X)) ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _ ≪≫
  (Q R).mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat _ 0 0 rfl)

def transIso {K K' L : Cx R} (i : (Q R).obj K ≅ (Q R).obj K') (n : ℤ) :
    CohomologyClass K L n ≃+ CohomologyClass K' L n :=
  (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).trans
    ({ toFun := fun f => i.inv ≫ f, invFun := fun g => i.hom ≫ g,
       left_inv := fun f => by simp, right_inv := fun g => by simp,
       map_add' := fun f g => Preadditive.comp_add _ _ _ _ _ _ } : _ ≃+ _) |>.trans
    (CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).symm

theorem locSecA : LateralTheory.E.LocSecPf.LocSecA := fun R _ X F n => ⟨transIso R (isoQ R X) n⟩

end LateralTheory.E.LocSecPfA
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfB

def HomSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  ∃ e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X,
    ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)

def ClassSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0})
  (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X),
  (∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)) →
  ∀ (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem locSecB_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LocSecPf.LocSecB := by
  intro R _ X F n
  obtain ⟨e, he⟩ := h1 R X
  exact h2 R X e he F n

theorem LocSec_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPf.LocSec_of LateralTheory.E.LocSecPfA.locSecA (locSecB_of h1 h2)

end LateralTheory.E.LocSecPfB
end
end
