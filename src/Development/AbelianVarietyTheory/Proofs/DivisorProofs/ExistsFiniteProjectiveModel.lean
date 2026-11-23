module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyStructureSheafCohomologyModelOfQuasiIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheafStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_finite_projective_model : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧
      Nonempty (Model s K) := by
  intro R _ _ X s hP hF
  haveI := hP
  haveI := hF
  letI := algebraΓOfHom s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have := isAffineHom_diagonal_of_isSeparated s
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := GlobalTheory.isAffineOpen_finset_biInf hD
  have hM : (LB.triv X).IsLB := LB.isLB_triv X
  have := Twist.isFiniteQC_twist (F := structureModule X) hM
  obtain ⟨K, φ, h1, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (R := R) (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) m
      (fun p hp => GlobalTheory.AbLaw.isZero_cechLB_X s (LB.triv X) _ (by rw [Fintype.card_fin]; exact hp.le))
      (GlobalTheory.AbLaw.flat_cechLB_X s hM hD') (fun n => by
        obtain ⟨e⟩ := GlobalTheory.FieldChangeInter.nonempty_coh_equiv s hM hc hD' n
        have := GlobalTheory.ProperFinite.finite_coh_of_isProper s (twist (structureModule X) (LB.triv X)) n
        exact Module.Finite.equiv e.symm)
  have hsep : IsSeparated s := inferInstance
  have hDa : ∀ i, IsAffineOpen (D i) := fun i => hD i
  obtain ⟨MC⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology R X s (Fin m) D hsep hDa hc
  exact ⟨K, fun p => ⟨h2 p, h4 p⟩, ⟨m, h1⟩, GlobalTheory.T.nonempty_structureSheafCohomologyModel_of_quasiIso R X s K _ φ (fun S _ _ => h7 S) MC⟩

end GlobalTheory.AbCoh
