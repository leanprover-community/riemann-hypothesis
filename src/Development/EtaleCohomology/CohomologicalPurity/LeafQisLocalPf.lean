module

public import Development.EtaleCohomology.CohomologicalPurity.LeafLocCutAug
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.QisLocalPf

variable (R : Type) [CommRing R]

abbrev Fsh := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))

instance wlb : Scheme.etaleTopology.{0}.WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

instance ph : (Fsh R).PreservesHomology := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

theorem chainsN_eq : chainsN R = TubeCut.chainsP R ⋙ (Fsh R).mapHomologicalComplex _ := by
  unfold chainsN TubeCut.chainsP
  rw [Functor.assoc, AlgebraicTopology.map_alternatingFaceMapComplex]
  rfl

theorem isIso_F_map {P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (g : P ⟶ Q)
    (hi : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} g)
    (hs : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} g) : IsIso ((Fsh R).map g) := by
  exact (GrothendieckTopology.W_iff _ g).1 ((GrothendieckTopology.W_iff_isLocallyBijective _ g).2 ⟨hi, hs⟩)

theorem sc_iso {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [IsIso (F.map (ShortComplex.homologyMap φ))] :
    IsIso (@ShortComplex.homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _) := by
  have e := ShortComplex.mapHomologyIso_hom_naturality φ F
  rw [(Iso.eq_comp_inv _).2 e]
  infer_instance

theorem quasiIso_chainsN {E E' : Spc} (f : E ⟶ E')
    (hi : ∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n))
    (hs : ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n)) :
    QuasiIso ((chainsN R).map f) := by
  have key : ∀ {K L : ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ} (φ : K ⟶ L),
      (∀ n, IsIso ((Fsh R).map (HomologicalComplex.homologyMap φ n))) →
      QuasiIso (((Fsh R).mapHomologicalComplex _).map φ) := by
    intro K L φ h
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
    have e := ShortComplex.mapHomologyIso_hom_naturality ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (Fsh R)
    have : IsIso ((Fsh R).map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))) := h n
    exact sc_iso (Fsh R) ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)
  have hf := key ((TubeCut.chainsP R).map f) (fun n => isIso_F_map R _ (hi n) (hs n))
  rw [chainsN_eq]
  exact hf

theorem LeafQisLocal_of : TubeCut.LeafQisLocal := by
  intro R _ E E' f hi hs
  have h := quasiIso_chainsN R f hi hs
  show QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h

end LateralTheory.CohomologicalPurity.QisLocalPf
