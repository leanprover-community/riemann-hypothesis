module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory Enriched.FunctorCategory
open scoped MonoidalClosed

namespace GlobalTheory.Et

section Site

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

instance (F G : Cᵒᵖ ⥤ ModuleCat.{1} S) : HasFunctorEnrichedHom (ModuleCat.{1} S) F G := inferInstance

instance (F G : Cᵒᵖ ⥤ ModuleCat.{1} S) : HasEnrichedHom (ModuleCat.{1} S) F G := inferInstance

instance : (J.W (A := ModuleCat.{1} S)).IsMonoidal := GrothendieckTopology.W.monoidal

instance : MonoidalClosed (Cᵒᵖ ⥤ ModuleCat.{1} S) := MonoidalClosed.FunctorCategory.monoidalClosed

theorem preservesFiniteLimits_tensorLeft_presheaf (P : Cᵒᵖ ⥤ ModuleCat.{1} S) (hP : ∀ U, Module.Flat S (P.obj U)) :
    PreservesFiniteLimits (tensorLeft P) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
  intro U
  have : Module.Flat S (P.obj U) := hP U
  have e : (evaluation Cᵒᵖ (ModuleCat.{1} S)).obj U ⋙ tensorLeft (P.obj U) ≅
      tensorLeft P ⋙ (evaluation Cᵒᵖ (ModuleCat.{1} S)).obj U := NatIso.ofComponents (fun F => Iso.refl _) (by
        intro F G g
        simp)
  exact preservesLimitsOfShape_of_natIso e

variable [HasSheafify J (ModuleCat.{1} S)]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

def tensorLeftSheafifyIso (P : Cᵒᵖ ⥤ ModuleCat.{1} S) :
    tensorLeft ((presheafToSheaf J _).obj P) ≅ sheafToPresheaf J _ ⋙ tensorLeft P ⋙ presheafToSheaf J _ :=
  NatIso.ofComponents (fun F => whiskerLeftIso _ (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J _) P F.obj) (by
    intro F G g
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, asIso_inv, Functor.Monoidal.μIso_hom]
    have h : g ≫ inv ((sheafificationAdjunction J _).counit.app G) =
        inv ((sheafificationAdjunction J _).counit.app F) ≫ (presheafToSheaf J _).map ((sheafToPresheaf J _).map g) := by
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact ((sheafificationAdjunction J _).counit.naturality g).symm
    change _ ◁ g ≫ _ = _ ≫ (presheafToSheaf J _).map (P ◁ (sheafToPresheaf J _).map g)
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, h, MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (Functor.LaxMonoidal.μ_natural_right (presheafToSheaf J (ModuleCat.{1} S)) P
      ((sheafToPresheaf J _).map g)))

theorem preservesFiniteLimits_tensorLeft_sheafify (P : Cᵒᵖ ⥤ ModuleCat.{1} S) (hP : ∀ U, Module.Flat S (P.obj U)) :
    PreservesFiniteLimits (tensorLeft ((presheafToSheaf J _).obj P)) := by
  have := preservesFiniteLimits_tensorLeft_presheaf S P hP
  exact preservesFiniteLimits_of_natIso (tensorLeftSheafifyIso J S P).symm

end Site

section Lin

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

instance tensorLeft_presheaf_additive (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : (tensorLeft P).Additive where
  map_add {F G} f g := by
    ext U : 2
    exact MonoidalPreadditive.whiskerLeft_add ..

instance tensorLeft_presheaf_linear (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : (tensorLeft P).Linear S where
  map_smul {F G} f r := by
    ext U : 2
    exact MonoidalLinear.whiskerLeft_smul ..

variable [HasSheafify J (ModuleCat.{1} S)]

instance presheafToSheaf_linear : (presheafToSheaf J (ModuleCat.{1} S)).Linear S where
  map_smul {P Q} f r := by
    let adj := sheafificationAdjunction J (ModuleCat.{1} S)
    apply (adj.homEquiv P ((presheafToSheaf J _).obj Q)).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit]
    have h1 := adj.unit.naturality (r • f)
    have h2 := adj.unit.naturality f
    dsimp at h1 h2
    change adj.unit.app P ≫ ((presheafToSheaf J (ModuleCat.{1} S)).map (r • f)).hom =
      adj.unit.app P ≫ (r • ((presheafToSheaf J (ModuleCat.{1} S)).map f).hom)
    rw [Linear.comp_smul, ← h2, ← h1, Linear.smul_comp]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

theorem tensorLeft_sheaf_additive (F : Sheaf J (ModuleCat.{1} S)) : (tensorLeft F).Additive := by
  have e : tensorLeft F ≅ sheafToPresheaf J _ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _ :=
    (tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      tensorLeftSheafifyIso J S F.obj
  exact Functor.additive_of_iso e.symm

theorem tensorLeft_sheaf_linear (F : Sheaf J (ModuleCat.{1} S)) :
    (letI := tensorLeft_sheaf_additive J S F; (tensorLeft F).Linear S) := by
  letI := tensorLeft_sheaf_additive J S F
  have e : tensorLeft F ≅ sheafToPresheaf J _ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _ :=
    (tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      tensorLeftSheafifyIso J S F.obj
  exact Functor.linear_of_iso S e.symm

end Lin

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

instance : MonoidalCategory (Shv R) := Sheaf.monoidalCategory _ _

instance : SymmetricCategory (Shv R) := Sheaf.symmetricCategory _ _

instance : MonoidalClosed (Shv R) := Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance (F : Shv R) : (tensorLeft F).Additive := tensorLeft_sheaf_additive _ _ F

instance (F : Shv R) : (tensorLeft F).Linear (ULift.{1} R) := tensorLeft_sheaf_linear _ _ F

instance (F : Shv R) : (tensorRight F).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight F)

instance (F : Shv R) : (tensorRight F).Linear (ULift.{1} R) :=
  Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight F)

instance (F : Shv R) : PreservesFiniteColimits (tensorRight F) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)

abbrev freePre (X : Scheme.{0}) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) :=
  uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R)

instance (X : Scheme.{0}) : PreservesFiniteLimits (tensorLeft ((freeOn R).obj X)) :=
  preservesFiniteLimits_tensorLeft_sheafify _ _ (freePre R X) (fun U =>
    inferInstanceAs (Module.Flat (ULift.{1} R) (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R)))

class FlatCoef : Prop where
  preservesFiniteLimits_tensorRight : PreservesFiniteLimits (tensorRight (coef R))

attribute [instance] FlatCoef.preservesFiniteLimits_tensorRight

def coefMulPre : coefPre R ⊗ coefPre R ⟶ coefPre R where
  app U := ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ (ULift.{1} R)
    (fun f g : ULift.{1} C(U.unop, R) => (⟨f.down * g.down⟩ : ULift.{1} C(U.unop, R)))
    (fun _ _ _ => ULift.ext (add_mul _ _ _))
    (fun c _ _ => ULift.ext (smul_mul_assoc c.down _ _))
    (fun _ _ _ => ULift.ext (mul_add _ _ _))
    (fun c _ _ => ULift.ext (mul_smul_comm c.down _ _))))
  naturality U V f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl

def coefOnePre : 𝟙_ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ⟶ coefPre R where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (⟨1⟩ : ULift.{1} C(U.unop, R)))
  naturality U V f := by
    ext c
    exact ULift.ext (ContinuousMap.ext fun x => rfl)

def freeDiagPre (X : Scheme.{0}) : freePre R X ⟶ freePre R X ⊗ freePre R X where
  app U := ModuleCat.ofHom (Finsupp.linearCombination (ULift.{1} R)
    (fun f => ((Finsupp.single f (1 : ULift.{1} R) : (freePre R X).obj U) ⊗ₜ[ULift.{1} R]
      (Finsupp.single f (1 : ULift.{1} R) : (freePre R X).obj U))))
  naturality U V g := by
    apply ModuleCat.hom_ext
    refine Finsupp.lhom_ext (fun f c => ?_)
    change Finsupp.linearCombination _ _ (Finsupp.mapDomain _ (Finsupp.single f c)) =
      ((freePre R X ⊗ freePre R X).map g).hom (Finsupp.linearCombination _ _ (Finsupp.single f c))
    rw [Finsupp.mapDomain_single]
    erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
    congr 1
    exact (congrArg₂ (fun (a b : (freePre R X).obj V) => a ⊗ₜ[ULift.{1} R] b) Finsupp.mapDomain_single Finsupp.mapDomain_single).symm

def freeAugPre (X : Scheme.{0}) : freePre R X ⟶ 𝟙_ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) where
  app U := ModuleCat.ofHom (Finsupp.linearCombination (ULift.{1} R) (fun _ => (1 : ULift.{1} R)))
  naturality U V g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro f
    apply LinearMap.ext_ring
    change Finsupp.linearCombination _ _ (Finsupp.mapDomain _ (Finsupp.single f 1)) =
      Finsupp.linearCombination (ULift.{1} R) (fun _ => (1 : ULift.{1} R)) (Finsupp.single f 1)
    simp [Finsupp.mapDomain_single]

def coefMul : coef R ⊗ coef R ⟶ coef R :=
  Functor.LaxMonoidal.μ (presheafToSheaf _ _) (coefPre R) (coefPre R) ≫ (presheafToSheaf _ _).map (coefMulPre R)

def coefOne : 𝟙_ (Shv R) ⟶ coef R :=
  Functor.LaxMonoidal.ε (presheafToSheaf _ _) ≫ (presheafToSheaf _ _).map (coefOnePre R)

def freeDiag (X : Scheme.{0}) : (freeOn R).obj X ⟶ (freeOn R).obj X ⊗ (freeOn R).obj X :=
  (presheafToSheaf _ _).map (freeDiagPre R X) ≫ Functor.OplaxMonoidal.δ (presheafToSheaf _ _) _ _

def freeAug (X : Scheme.{0}) : (freeOn R).obj X ⟶ 𝟙_ (Shv R) :=
  (presheafToSheaf _ _).map (freeAugPre R X) ≫ Functor.OplaxMonoidal.η (presheafToSheaf _ _)

section Cup

variable [FlatCoef R]

def cupExt (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a : HS R (coef R) i X) (b : HS R (coef R) j X) :
    HS R (coef R) n X :=
  (Abelian.Ext.mk₀ (freeDiag R X)).comp ((b.mapExactFunctor (tensorLeft ((freeOn R).obj X))).comp
    ((a.mapExactFunctor (tensorRight (coef R))).comp (Abelian.Ext.mk₀ (coefMul R)) (add_zero i))
    (show j + i = n by omega)) (zero_add n)

private theorem extComp_isLinear {S D : Type*} [CommRing S] [Category* D] [Abelian D]
    [HasExt.{1} D] [Linear S D] {A B C M N : D} {i j n : ℕ} (h : j + i = n)
    (f : Abelian.Ext A B i →ₗ[S] Abelian.Ext M N i)
    (g : Abelian.Ext A B j →ₗ[S] Abelian.Ext C M j)
    (d : Abelian.Ext A C 0) (m : Abelian.Ext N B 0)
    (product : Abelian.Ext A B i → Abelian.Ext A B j → Abelian.Ext A B n)
    (hprod : product = fun a b => d.comp ((g b).comp ((f a).comp m (add_zero i)) h) (zero_add n)) :
    (∀ b, IsLinearMap S (fun a => product a b)) ∧
      (∀ a, IsLinearMap S (product a)) := by
  subst product
  let precomp := d.precompOfLinear S B (zero_add n)
  constructor
  · intro b
    exact (precomp.comp (((g b).precompOfLinear S B h).comp
      ((m.postcompOfLinear S M (add_zero i)).comp f))).isLinear
  · intro a
    exact (precomp.comp ((((f a).comp m (add_zero i)).postcompOfLinear S C h).comp g)).isLinear

private theorem cupExt_isLinear (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) :
    (∀ b : HS R (coef R) j X,
      IsLinearMap (ULift.{1} R) (fun a : HS R (coef R) i X => cupExt R X h a b)) ∧
    (∀ a : HS R (coef R) i X,
      IsLinearMap (ULift.{1} R) (fun b : HS R (coef R) j X => cupExt R X h a b)) := by
  let A := (freeOn R).obj X
  let B := coef R
  exact extComp_isLinear ((Nat.add_comm j i).trans h)
    ((tensorRight B).mapExtLinearMap (ULift.{1} R) A B i)
    ((tensorLeft A).mapExtLinearMap (ULift.{1} R) A B j)
    (Abelian.Ext.mk₀ (freeDiag R X)) (Abelian.Ext.mk₀ (coefMul R))
    (cupExt R X h) rfl

theorem cupExt_add_left (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a a' : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h (a + a') b = cupExt R X h a b + cupExt R X h a' b := by
  exact ((cupExt_isLinear R X h).1 b).map_add a a'

theorem cupExt_add_right (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a : HS R (coef R) i X)
    (b b' : HS R (coef R) j X) : cupExt R X h a (b + b') = cupExt R X h a b + cupExt R X h a b' := by
  exact ((cupExt_isLinear R X h).2 a).map_add b b'

theorem cupExt_smul_left (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (r : ULift.{1} R) (a : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h (r • a) b = r • cupExt R X h a b := by
  exact ((cupExt_isLinear R X h).1 b).map_smul r a

theorem cupExt_smul_right (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (r : ULift.{1} R) (a : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h a (r • b) = r • cupExt R X h a b := by
  exact ((cupExt_isLinear R X h).2 a).map_smul r b

def cupN (X : Scheme.{0}) (i j n : ℕ) (h : i + j = n) : H R i X →ₗ[R] H R j X →ₗ[R] H R n X :=
  LinearMap.mk₂ R (fun a b => cupExt R X h a b)
    (fun a a' b => cupExt_add_left R X h a a' b)
    (fun r a b => cupExt_smul_left R X h (ULift.up r) a b)
    (fun a b b' => cupExt_add_right R X h a b b')
    (fun r a b => cupExt_smul_right R X h (ULift.up r) a b)

def cup (X : Scheme.{0}) (i j : ℕ) : H R i X →ₗ[R] H R j X →ₗ[R] H R (i + j) X := cupN R X i j (i + j) rfl

end Cup


variable [FlatCoef R]


section DegreeZero

variable [FlatCoef R]

def ofPre {X : Scheme.{0}} (γ : freePre R X ⟶ coefPre R) : H R 0 X := Abelian.Ext.mk₀ ((presheafToSheaf _ _).map γ)

private theorem ext_tensor_mk₀ {D : Type*} [Category* D] [Abelian D] [HasExt.{1} D]
    [MonoidalCategory D] {A B : D} [(tensorLeft A).Additive] [(tensorRight B).Additive]
    [PreservesFiniteLimits (tensorLeft A)] [PreservesFiniteLimits (tensorRight B)]
    [PreservesFiniteColimits (tensorLeft A)] [PreservesFiniteColimits (tensorRight B)]
    (d : A ⟶ A ⊗ A) (g g' : A ⟶ B) (m : B ⊗ B ⟶ B) :
    (Abelian.Ext.mk₀ d).comp (((Abelian.Ext.mk₀ g').mapExactFunctor (tensorLeft A)).comp
      (((Abelian.Ext.mk₀ g).mapExactFunctor (tensorRight B)).comp (Abelian.Ext.mk₀ m) (add_zero 0))
      (zero_add 0)) (zero_add 0) = Abelian.Ext.mk₀ (d ≫ (g ⊗ₘ g') ≫ m) := by
  simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  exact congrArg (fun f => Abelian.Ext.mk₀ (d ≫ f))
    (MonoidalCategory.tensorHom_def'_assoc g g' m).symm

theorem cupExt_mk₀ (X : Scheme.{0}) (g g' : (freeOn R).obj X ⟶ coef R) :
    cupExt R X (rfl : 0 + 0 = 0) (Abelian.Ext.mk₀ g) (Abelian.Ext.mk₀ g') =
      Abelian.Ext.mk₀ (freeDiag R X ≫ (g ⊗ₘ g') ≫ coefMul R) := by
  exact ext_tensor_mk₀ (freeDiag R X) g g' (coefMul R)

theorem cupN_ofPre (X : Scheme.{0}) (γ γ' : freePre R X ⟶ coefPre R) :
    cupN R X 0 0 0 rfl (ofPre R γ) (ofPre R γ') = ofPre R (freeDiagPre R X ≫ (γ ⊗ₘ γ') ≫ coefMulPre R) := by
  refine (cupExt_mk₀ R X _ _).trans (congrArg Abelian.Ext.mk₀ ?_)
  simp only [freeDiag, coefMul, Functor.map_comp]
  erw [Category.assoc, Functor.OplaxMonoidal.δ_natural_assoc, Functor.Monoidal.δ_μ_assoc]
  rfl

theorem e_ofPre (X : Scheme.{0}) (γ : freePre R X ⟶ coefPre R) :
    H0.e R X (ofPre R γ) = (γ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1)).down := by
  have h1 : (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _
      ((presheafToSheaf _ _).map γ) = γ ≫ toSheafify _ (coefPre R) := by
    rw [Adjunction.homEquiv_unit]
    exact ((sheafificationAdjunction _ _).unit.naturality γ).symm
  have h0 : Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (ofPre R γ) = (presheafToSheaf _ _).map γ :=
    Abelian.Ext.addEquiv₀.apply_symm_apply _
  have key : H0.e R X (ofPre R γ) = AddEquiv.ulift ((((isoSheafify _ (H0.sh R)).app (op X)).symm.toLinearEquiv)
      (H0.yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (ofPre R γ))))) := rfl
  rw [key, h0]
  erw [h1]
  have h3 := ConcreteCategory.congr_hom ((isoSheafify _ (H0.sh R)).hom_inv_id_app (op X))
    (γ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1))
  rw [isoSheafify_hom] at h3
  exact congrArg ULift.down h3

theorem homEquiv_map_ofPre {X : Scheme.{0}} (γ : freePre R X ⟶ coefPre R) :
    (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _
      ((presheafToSheaf _ _).map γ) = γ ≫ toSheafify _ (coefPre R) := by
  rw [Adjunction.homEquiv_unit]
  exact ((sheafificationAdjunction _ _).unit.naturality γ).symm

theorem exists_ofPre {X : Scheme.{0}} (x : H R 0 X) : ∃ γ : freePre R X ⟶ coefPre R, ofPre R γ = x := by
  let e := H0.yonedaAdd R X (coefPre R)
  let v : (coefPre R).obj (op X) := ULift.up (H0.e R X x)
  refine ⟨e.symm v, (H0.e R X).injective ?_⟩
  exact (e_ofPre R X (e.symm v)).trans (congrArg ULift.down (e.apply_symm_apply v))

theorem e_cupN (X : Scheme.{0}) (x y : H R 0 X) :
    H0.e R X (cupN R X 0 0 0 rfl x y) = H0.e R X x * H0.e R X y := by
  obtain ⟨γ, rfl⟩ := exists_ofPre R x
  obtain ⟨γ', rfl⟩ := exists_ofPre R y
  rw [cupN_ofPre, e_ofPre, e_ofPre, e_ofPre]
  change ((coefMulPre R).app (op X) (((γ ⊗ₘ γ').app (op X)) ((freeDiagPre R X).app (op X)
    (Finsupp.single (ULift.up (𝟙 X)) 1)))).down = _
  erw [Finsupp.linearCombination_single, one_smul]
  rfl

theorem e_cup (X : Scheme.{0}) (x y : H R 0 X) : H0.e R X (cup R X 0 0 x y) = H0.e R X x * H0.e R X y :=
  e_cupN R X x y

end DegreeZero

section One

variable [FlatCoef R]

def one (X : Scheme.{0}) : H R 0 X := Abelian.Ext.mk₀ (freeAug R X ≫ coefOne R)

theorem one_eq_ofPre (X : Scheme.{0}) : one R X = ofPre R (freeAugPre R X ≫ coefOnePre R) := by
  refine congrArg Abelian.Ext.mk₀ ?_
  simp only [freeAug, coefOne, Functor.map_comp]
  erw [Category.assoc, Functor.Monoidal.η_ε_assoc]

theorem e_one (X : Scheme.{0}) : H0.e R X (one R X) = 1 := by
  rw [one_eq_ofPre, e_ofPre]
  change ((coefOnePre R).app (op X) ((freeAugPre R X).app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1))).down = 1
  erw [Finsupp.linearCombination_single]
  ext x
  change ((((1 : ULift.{1} R) • (1 : ULift.{1} R)) • (⟨1⟩ : ULift.{1} C(X, R))).down) x = (1 : C(X, R)) x
  simp

end One


variable (X : Scheme.{0})


end GlobalTheory.Et
