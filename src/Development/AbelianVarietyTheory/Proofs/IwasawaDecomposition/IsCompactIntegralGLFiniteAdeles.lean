module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
public import Mathlib.Topology.Instances.Matrix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory

theorem isCompact_matInt_set (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} := by
  have hO : IsCompact ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) :
      Set (FiniteAdeleRing (𝓞 F) F)) := PI.WAU.isCompact_Ohat (F := F)
  have h := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hO))
  have he : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} =
      Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n =>
        ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F)))) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [he]
  exact h

theorem isCompact_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact (PIW.ClassFinD.KGL F n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  have hA := isCompact_matInt_set F n
  have hA' := (MulOpposite.opHomeomorph
    (M := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).symm.isCompact_preimage.2 hA
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).isCompact_preimage (hA.prod hA')
  convert h using 1
  ext g
  exact Iff.rfl

end GlobalTheory
