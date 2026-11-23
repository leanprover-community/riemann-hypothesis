module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingEquivPowerSeriesOfComplete
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CurveDVR
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
public import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field

@[expose] public section

open Polynomial Matrix

private theorem UpperTheory.V.Pr.T.curveNorm_coeffField {A : Type} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Finite (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP A p] :
    ∃ ι : IsLocalRing.ResidueField A →+* A,
      Function.Surjective ((IsLocalRing.residue A).comp ι) := by
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  haveI : Algebra.FormallySmooth (ZMod p) (IsLocalRing.ResidueField A) := by
    haveI : Module.Finite (ZMod p) (IsLocalRing.ResidueField A) := Module.Finite.of_finite
    haveI : Algebra.FormallyEtale (ZMod p) (IsLocalRing.ResidueField A) :=
      Algebra.FormallyEtale.of_isSeparable _ _
    infer_instance
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (R := ZMod p) (A := IsLocalRing.ResidueField A) (I := IsLocalRing.maximalIdeal A)
    (AlgHom.id (ZMod p) (IsLocalRing.ResidueField A))
  refine ⟨g.toRingHom, fun y => ⟨y, ?_⟩⟩
  exact AlgHom.congr_fun hg y

theorem UpperTheory.V.Pr.T.curveNorm :
    ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
      (p : ℕ) [Fact p.Prime] [CharP R p], ringKrullDim R = 1 →
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (f : R →+* PowerSeries k),
        Function.Injective f ∧ IsLocalHom f ∧ f.Finite := by
  intro R _ _ _ _ _ _ p _ _ hdim
  obtain ⟨A, _, _, _, f, hc, hfin, hinj, hloc, hf⟩ := UpperTheory.V.Pr.T.curveDVR (R := R) p hdim
  haveI : CharP A p := charP_of_injective_ringHom hinj p
  obtain ⟨ι, hι⟩ := UpperTheory.V.Pr.T.curveNorm_coeffField (A := A) p
  obtain ⟨e, -⟩ := GlobalTheory.ArcAvoid.exists_ringEquiv_powerSeries_of_complete ι hι
  refine ⟨IsLocalRing.ResidueField A, inferInstance, hfin,
    (e.symm : A →+* PowerSeries _).comp f, e.symm.injective.comp hinj, ?_, ?_⟩
  · haveI : IsLocalHom (e.symm : A →+* PowerSeries (IsLocalRing.ResidueField A)) :=
      isLocalHom_equiv e.symm |>.1 |> fun h => ⟨h⟩
    exact RingHom.isLocalHom_comp _ _
  · exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp hf
