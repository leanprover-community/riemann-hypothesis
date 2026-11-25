module

public import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.InertAll

theorem nonSplitAt_of_forall (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (hns : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) : GlobalTheory.WeilParts.NonSplitAt D v ε := by
  refine ⟨hε, fun ⟨e, he, heq⟩ => ?_⟩
  have k := hns e he
  have e0 : e = 0 := by
    rw [← heq, mul_add, he.1, he.2.1, add_zero] at k
    exact k
  rw [e0, map_zero, zero_add] at heq
  obtain ⟨α, rfl, h1, -⟩ := hε
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have : pairA D.host.F 0 α = 0 := hinj (by rw [map_zero]; exact heq.symm)
  have : α = 0 := congrArg Prod.snd this
  rw [this, map_zero] at h1
  exact zero_ne_one h1

theorem unramAt_of_unrAtV (D : D7) (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) (hχ : Formalism.IndefR.WeilFull.UnrAtV ε χ) : GlobalTheory.WeilParts.UnramAt ε χ :=
  fun x hx i1 i2 => hχ x (by linear_combination (-1 : AE D) * hx) i1 i2

theorem inertAllO_of_eta (D : D7) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) : Formalism.IndefR.WeilFull.InertAllO D := by
  intro ψ S T χS χT om H _ _ ΛS ΛT hS hT βS βT hβS hβT v ε hε _ hns uS uT g h sg sh hg hh f hf hvac
  have hv : GlobalTheory.WeilParts.NonSplitAt D v ε := nonSplitAt_of_forall D v ε hε hns
  have hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) :=
    fun u => GlobalTheory.LatStab.mem_latO_iff_actO_mem D S T ΛS ΛT βS βT hS.1 hT.1 hβS hβT g h hg hh _ u
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := by
    intro u hu
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
    have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
    rwa [h1] at h2
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ H.std S T ΛS ΛT hS hT χS χT om hη H v ε hv (unramAt_of_unrAtV D ε χS uS) (unramAt_of_unrAtV D ε χT uT) g h sg sh hst f hf hfix

theorem inertAllO : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D :=
  fun D => inertAllO_of_eta D (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D)

end GlobalTheory.InertAll
