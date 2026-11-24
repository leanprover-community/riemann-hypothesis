module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
public import GroundTheory.GlobalFields.Adele.Compact
public import GroundTheory.GlobalFields.Adele.Discrete
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.GlobalFields.Adele.Approximation

@[expose] public section

open UpperTheory.V.Sd.Eis

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
private theorem cont_nilM (F : Type) [Field F] [NumberField F] :
    Continuous (fun x : NA F => (nilM x : Matrix (Fin 2) (Fin 2) (Ad F))) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
theorem UpperTheory.eisenstein_constantTerm_upperBlock :
    UpperTheory.V.Sd.Eis.BlockTop := by
  intro F _ _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact (Set.countable_range _).to_subtype
  · obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
    have hD : IsCompact (C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :
        Set (Ad F)) := hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
    refine ⟨_, isCompact_univ_pi fun _ : BlockIx 2 1 => hD, fun x => ?_⟩
    choose k hk using hx
    exact ⟨fun p => algebraMap F (Ad F) (k (x p)), ⟨fun p => k (x p), rfl⟩, fun p _ => hk (x p)⟩
  · exact Units.continuous_iff.2 ⟨continuous_const.add (cont_nilM F), continuous_const.sub (cont_nilM F)⟩
  · intro x
    refine Units.ext ?_
    change 1 + nilM x = !![((1 : (Ad F)ˣ) : Ad F), x ⟨(0, 1), by decide⟩; 0, 1]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [nilM]
