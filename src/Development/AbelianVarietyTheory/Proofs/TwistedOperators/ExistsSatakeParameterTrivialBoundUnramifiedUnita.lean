module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTrivialBoundInertPlaceUnitarisableSphericaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalEigenvectorGeneratesIrreducibleSubrepreStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LFun.SatCompare in
theorem GlobalTheory.Twist.satParam_exists_trivialBound : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KU σ n) → (∀ h ∈ Hecke ℂ (KU σ n), ∃ c : ℂ, heckeVec ρ (KU σ n) h x = c • x) → ∃ α, IsSatVecU ϖ q ρ x α ∧ GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hρ x hx0 hxK hxH
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  obtain ⟨U, hU', hxU, hirr, hun, hline⟩ :=
    GlobalTheory.T.spherical_eigenvector_generates_irreducible_subrepresentation ρ (KU σ n) ho (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) hρ x hx0 hxK hxH
  set π := GlobalTheory.PRep.sub ρ U hU'
  set x' : U := ⟨x, hxU⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hx'K : x' ∈ fixed π (KU σ n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxK k hk)
  have hs : GlobalTheory.LGrp.IsSpherical π (KU σ n) := (Submodule.ne_bot_iff _).2 ⟨x', hx'K, hx'0⟩
  have hf : FiniteDimensional ℂ (fixed π (KU σ n)) := by
    have hle : fixed π (KU σ n) ≤ Submodule.span ℂ {x'} := fun y hy => by
      obtain ⟨c, rfl⟩ := hline y hy
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    exact Submodule.finiteDimensional_of_le hle
  obtain ⟨α, hα⟩ := exists_hasSatU hU hirr hf hs
  refine ⟨α, ?_, GlobalTheory.T.satakeTrivialBound_inertPlace_unitarisable_spherical L ϖ σ q n hU U π α hirr hun hα⟩
  have := (hα.2 x' hx'K hx'0).map hU U.subtype (fun g y => rfl) hx0
  exact this
