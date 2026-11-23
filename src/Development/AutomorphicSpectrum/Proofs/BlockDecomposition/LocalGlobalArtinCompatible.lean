module

public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink


open GroundTheory.Global GroundTheory.Global.SemiLocal in
theorem local_restriction_abelianization_artin : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  intro E Ω _ _ _ _ _ w Ωv _ _ _ j hj a σ g hgj hloc L _ _
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨w'⟩ := GroundTheory.Global.IdeleGroup.nonempty_placesOver_of_finite (K := E) (L := L) w
  haveI : IsSepClosed Ωv := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  haveI : Algebra.IsSeparable (w.adicCompletion E) (w'.1.adicCompletion L) := inferInstance
  let ι : w'.1.adicCompletion L →ₐ[w.adicCompletion E] Ωv := IsSepClosed.lift
  set s := restrictAb L (le_maximalAbelianExtension L)
    (artinMap E Ω (GroundTheory.Global.IdeleClassGroup.mk E (IdeleGroup.finiteEmbedding w a))) with hs
  have hres : PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) = s :=
    congrArg (restrictAb L (le_maximalAbelianExtension L))
      ((topologicalAbelianizationEquiv E Ω).apply_symm_apply _)
  have h1 : ∀ l : L, ι (algebraMap L (w'.1.adicCompletion L) (s l)) =
      g (ι (algebraMap L (w'.1.adicCompletion L) l)) := fun l => by
    rw [hs, artinMap_finiteEmbedding_apply L w w' ι a l]
    exact hloc _ _
  rw [hres, PositivityTheory.FamInh.res_toAb]
  letI : Algebra E Ωv := ((algebraMap (w.adicCompletion E) Ωv).comp (algebraMap E (w.adicCompletion E))).toAlgebra
  let m₂ : L →ₐ[E] Ωv :=
    { toRingHom := j.comp (algebraMap L Ω)
      commutes' := fun y => by
        show j (algebraMap L Ω (algebraMap E L y)) = _
        rw [← IsScalarTower.algebraMap_apply]
        exact hj y }
  have hcomp : ∀ y : E, algebraMap L (w'.1.adicCompletion L) (algebraMap E L y) =
      algebraMap (w.adicCompletion E) (w'.1.adicCompletion L) (algebraMap E (w.adicCompletion E) y) := by
    intro y
    rw [← IsScalarTower.algebraMap_apply E L (w'.1.adicCompletion L),
      ← IsScalarTower.algebraMap_apply E (w.adicCompletion E) (w'.1.adicCompletion L)]
  let m₁ : L →ₐ[E] Ωv :=
    { toRingHom := (ι : w'.1.adicCompletion L →+* Ωv).comp (algebraMap L (w'.1.adicCompletion L))
      commutes' := fun y => by
        show ι (algebraMap L (w'.1.adicCompletion L) (algebraMap E L y)) = _
        rw [hcomp, ι.commutes]
        rfl }
  letI : Algebra L Ωv := m₂.toRingHom.toAlgebra
  haveI : IsScalarTower E L Ωv := IsScalarTower.of_algebraMap_eq fun y => (m₂.commutes y).symm
  let τ : L ≃ₐ[E] L := Normal.algHomEquivAut E Ωv L m₁
  have hτ : ∀ l : L, m₂ (τ l) = m₁ l := fun l =>
    DFunLike.congr_fun ((Normal.algHomEquivAut E Ωv L).symm_apply_apply m₁) l
  have h2 : ∀ l : L, τ (s l) = AlgEquiv.restrictNormalHom L σ (τ l) := fun l => by
    apply m₂.toRingHom.injective
    show m₂ (τ (s l)) = j (algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)))
    have hρ : algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)) = σ (algebraMap L Ω (τ l)) :=
      AlgEquiv.restrictNormal_commutes σ L (τ l)
    rw [hρ, ← hgj, hτ]
    have hj₂ : j (algebraMap L Ω (τ l)) = m₁ l := hτ l
    rw [hj₂]
    exact h1 l
  have h3 : τ * s = AlgEquiv.restrictNormalHom L σ * τ := AlgEquiv.ext h2
  have h4 : τ * s = τ * AlgEquiv.restrictNormalHom L σ := by
    rw [h3]
    exact IsMulCommutative.is_comm.comm _ _
  exact (mul_left_cancel h4).symm

end GlobalTheory.CompanionTheory.LTLink
