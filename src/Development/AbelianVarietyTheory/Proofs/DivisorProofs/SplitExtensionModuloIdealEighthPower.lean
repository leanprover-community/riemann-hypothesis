module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitPow

theorem splitExtensionModuloIdeal_eighth_power : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R),
    GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  intro R _ G₀ _ _ I ⟨E, ⟨D⟩⟩
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  obtain ⟨p, -⟩ := GlobalTheory.isPowGrp_baseChange _ _ (spMap (Ideal.Quotient.mk I)) (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8)
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Sp (R ⧸ I)) E.X (Fin 8 → E.X) 8 (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ _ _ (powObj E.B 8) E.B 8 p (powIsPowGrp E.B 8) D.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ _ _ 8 pT p D.i
  have hB : IsAbelianScheme (powObj E.B 8) := (GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp E.B 8)).2.2.2.1 E.isAbelian
  have hk := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ 8 pT p (powIsPowGrp E.B 8) D.i D.q i' q' hi hq D.isKernel
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G₀) := inferInstance
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj (powObj G₀ 8)) := inferInstance
  have hqc : QuasiCompact D.q.left := by
    have := D.q_affine
    infer_instance
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ (Fin 8 → E.X) _ (powObj E.B 8) hB q' i'
    (hq1 D.q_hom) (hi1 D.i_hom) (hq2 D.q_flat) (hq3 D.q_surjective) (hq4 hqc) hk
  obtain ⟨d, -, -⟩ := h hB
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory.SplitPow
end
