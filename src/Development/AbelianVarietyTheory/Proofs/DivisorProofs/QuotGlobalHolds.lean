module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedQuotientMapOfLocalQuotientsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalQuotientTransitionIsomorphismsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedQuotientMapFiniteFlatSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfChartsSurjectiveImageStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackGluedQuotientKernelPairOfCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
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

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

theorem quotGlobal_holds : QuotGlobal := by
  intro S _ A _ H _ i hA hi hm hf hfl
  have := hA.comm
  choose B instB q hq using GlobalTheory.T.exists_abelianQuotient_affineCover S A H i hA hi hm hf hfl
  have hfin : ∀ j, IsFinite (q j).left := fun j => (hq j).2.2.1
  have hflat : ∀ j, Flat (q j).left := fun j => (hq j).2.2.2.1
  have hsurj : ∀ j, Surjective (q j).left := fun j => (hq j).2.2.2.2.1
  have hqc : ∀ j, QuasiCompact (q j).left := fun j => by have := hfin j; infer_instance
  have hsq : ∀ j, _ := fun j => (hq j).2.2.2.2.2
  obtain ⟨b, hb1, hb2, hchar⟩ := GlobalTheory.T.exists_local_quotient_transition_isomorphisms S S.affineCover A H i B q hflat hsurj hqc hsq
  have hcoc := GlobalTheory.T.local_quotient_transition_cocycle S S.affineCover A H i B q b hflat hsurj hqc hb1 hchar
  obtain ⟨G0, F, ψ, hψ, hψ2⟩ := GlobalTheory.CocycleGlue.exists_glue (fun j => S.affineCover.X j) (fun j => (B j).left)
    (fun j => S.affineCover.f j) (fun j => inferInstance) (fun j => (B j).hom)
    (fun j k => pullback ((B j).hom ≫ S.affineCover.f j) (S.affineCover.f k)) (fun j k => pullback.fst _ _) b
    (fun j k => by rw [hb1]; exact IsPullback.of_hasPullback _ _) hb2 hcoc
  obtain ⟨Qm, hQF, hQm⟩ := GlobalTheory.T.exists_gluedQuotientMap_of_local_quotients S S.affineCover A H i B q b G0 F ψ hchar (fun j k => (hψ2 j k).w)
    (fun j => (hψ j).w)
  let G : Over S := Over.mk F
  let Q : A ⟶ G := Over.homMk Qm hQF
  have hpb : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q :=
    GlobalTheory.T.isPullback_gluedQuotient_kernelPair_of_cover S S.affineCover A H G i Q B ψ q hψ hQm hsq
  obtain ⟨hQfin, hQfl, hQs⟩ := GlobalTheory.T.gluedQuotientMap_finite_flat_surjective S S.affineCover A G Q B ψ q hψ hQm hfin hflat hsurj
  have : IsCommMonObj A := hA.comm
  have : IsMonHom i := hi
  have : QuasiCompact Q.left := inferInstance
  obtain ⟨instG, hcomm, hhom, -⟩ := GlobalTheory.AbelianQuotient.exists_grpObj i Q hpb
  exact ⟨G, instG, Q, GlobalTheory.T.isAbelianScheme_of_charts_surjective_image S S.affineCover A G Q B ψ hA hcomm hQs hψ (fun j => (hq j).1), hhom, hQfin, hQfl, hQs, hpb⟩

end GlobalTheory.IwLevel
