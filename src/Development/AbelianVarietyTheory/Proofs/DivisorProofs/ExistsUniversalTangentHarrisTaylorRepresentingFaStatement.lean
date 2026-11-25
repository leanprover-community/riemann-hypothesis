module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHodgeFiltrationNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Algebra.Azumaya.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

-- Representability uses the filtration results and the glued deformation.
-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylor, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylor =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylor", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformation\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCountStatement\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderIsoOfSameHodgeFiltration\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHodgeFiltrationNaturalityStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem GlobalTheory.HTUniv.main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨f, hdir, huniq⟩ := GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count p D R b N hN hNp k t o₀
  obtain ⟨o, m, hm⟩ := _root_.GlobalTheory.HTGlue.exists_glue p D R b N hN hNp k t o₀ _ f hdir
  refine ⟨o, ⟨m⟩, fun o' ho' => ?_⟩
  obtain ⟨m'⟩ := ho'
  have key : ∀ (s' : Sp (DualNumber k) ⟶ Sp R) (o'' : GlobalTheory.UPel.HT.Obj b N s')
      (m'' : GlobalTheory.UPel.HT.ObjMap o₀ o'' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
      (c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k)
      (n : GlobalTheory.UPel.HT.ObjMap o'' o (spMap (TrivSqZeroExt.map c).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m''.cart x (∑ j, c (Pi.single j 1) • f j x) := by
    intro s' o'' m'' c n x hx
    have h := _root_.GlobalTheory.HTUniv.Nat.main p D R b N hN hNp k t o₀ _ _ o m c s' o'' m'' n x _ (hm x hx)
    rw [GlobalTheory.HTUniv.comp_pi] at h
    exact h
  obtain ⟨c₀, hc₀, hc₀u⟩ := huniq o' m'
  let c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k := ∑ j, c₀ j • LinearMap.proj j
  have hcj : ∀ j, c (Pi.single j 1) = c₀ j := fun j => GlobalTheory.HTUniv.sum_proj_single c₀ j
  obtain ⟨oc, ⟨nc⟩⟩ := _root_.GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N _ _ _ (spMap (TrivSqZeroExt.map c).toRingHom) o
  have hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (TrivSqZeroExt.map c).toRingHom =
      spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom := by
    rw [← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext x
    simp
  obtain ⟨mc⟩ := (_root_.GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ oc o
    (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (spMap (TrivSqZeroExt.map c).toRingHom)).2
    (by rw [hcomp]; exact ⟨m⟩) ⟨nc⟩
  have hfc := key _ oc mc c nc
  simp only [hcj] at hfc
  obtain ⟨iso⟩ := _root_.GlobalTheory.HTFirstOrderIso.objMap_of_filLift p D R b N hN hNp k t o₀ _ _ o' oc m' mc (fun x => ∑ j, c₀ j • f j x) hc₀ hfc
  refine ⟨c, ?_, ?_⟩
  · have h := (_root_.GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' oc o (𝟙 _)
      (spMap (TrivSqZeroExt.map c).toRingHom)).1 ⟨iso⟩ ⟨nc⟩
    rwa [Category.id_comp] at h
  · rintro c' ⟨n'⟩
    have h1 := key _ o' m' c' n'
    have h2 := hc₀u (fun j => c' (Pi.single j 1)) h1
    refine LinearMap.ext fun v => ?_
    rw [GlobalTheory.HTUniv.coord c' v, GlobalTheory.HTUniv.coord c v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcj]
    exact congrArg _ (congrFun h2 j)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylor =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  first | (exact @GlobalTheory.HTUniv.main)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.RepTangent

alias spMap_id' := _root_.GlobalTheory.LevelFibre.spMap_id'

theorem exists_univ_tangent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  intro p _ D R _ _ b N hN hNp F _ _ k _ _ x
  obtain ⟨o₀, ⟨m₀⟩⟩ := _root_.GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N F.X (Sp k) F.s x F.univ
  obtain ⟨o, ⟨mo⟩, huniv⟩ := GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor p D R b N hN hNp k (x ≫ F.s) o₀
  obtain ⟨u, ⟨hu1, ⟨mu⟩⟩, -⟩ := F.rep _ _ o
  have hfst : spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫
      spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) = 𝟙 _ := by
    rw [_root_.GlobalTheory.spMap_comp_ring]
    convert spMap_id' k
    ext a; simp
  refine ⟨u, ?_, hu1, ?_⟩
  · obtain ⟨f, -, hf⟩ := F.rep _ _ o₀
    have e1 := hf x ⟨rfl, ⟨m₀⟩⟩
    have e2 := hf (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u)
      ⟨by rw [Category.assoc, hu1, ← Category.assoc, hfst, Category.id_comp], ⟨MapComp.comp mo mu⟩⟩
    exact e2.trans e1.symm
  · intro v hv1 hv2
    obtain ⟨o', ⟨m'⟩⟩ := _root_.GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N F.X (Sp (DualNumber k)) F.s v F.univ
    have main : ∀ (s₁ : Sp (DualNumber k) ⟶ Sp R) (o' : Obj b N s₁), s₁ = v ≫ F.s → ObjMap o' F.univ v →
        ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
      intro s₁ o' hs m'
      rw [hv2] at hs
      subst hs
      have h0 : Nonempty (ObjMap o₀ F.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) := by
        rw [hv1]; exact ⟨m₀⟩
      have m'' := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ o' F.univ _ v).2 h0 ⟨m'⟩
      obtain ⟨c, ⟨mc⟩, hc⟩ := huniv o' m''
      have hbase : ∀ c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k,
          (spMap (TrivSqZeroExt.map c).toRingHom ≫ u) ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s := by
        intro c
        rw [Category.assoc, hu1, ← Category.assoc, _root_.GlobalTheory.spMap_comp_ring]
        congr 2
        exact (TrivSqZeroExt.map c).comp_algebraMap
      refine ⟨c, ?_, ?_⟩
      · obtain ⟨f, -, hf⟩ := F.rep _ _ o'
        exact (hf v ⟨hv2, ⟨m'⟩⟩).trans (hf _ ⟨hbase c, ⟨MapComp.comp mc mu⟩⟩).symm
      · intro c' hc'
        apply hc
        rw [hc'] at m'
        exact (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' o F.univ _ u).2 ⟨m'⟩ ⟨mu⟩
    exact main _ o' rfl m'

end GlobalTheory.UPel.HT.RepTangent
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  first | (exact @GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement =====
