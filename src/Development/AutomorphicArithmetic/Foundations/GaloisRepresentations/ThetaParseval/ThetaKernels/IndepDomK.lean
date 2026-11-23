module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocCompactNAK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzJLeftInvK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzLeftInvK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousCjK

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
theorem indepDom_k : _root_.PositivityTheory.SiegelWeilFormula.Act.IndepDom_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf z
  have hE := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.eis_leftInv_k d hf z
  refine ⟨fun nb lam 𝓖 𝓖₀ h h₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hT x => ?_, fun nb' lam' 𝓖' 𝓖'₀ h' h'₀ T' x => ?_⟩
  · have step1 : ∀ g, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T g = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T g :=
      fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_dom_k d h h₀ _ hE T g
    simp_rw [step1]
    have := hU.2.1
    have : VAddInvariantMeasure L.ratV (Fin L.n → AE F E) ν := ⟨fun c s _ => measure_preimage_add ν c.1 s⟩
    have : Countable L.ratV := by
      have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
      refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
        (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
      obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
      exact ⟨v, Subtype.ext hv.symm⟩
    refine hU.2.2.1.setIntegral_eq hU₀.2.2.1 fun u₀ u => ?_
    show fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM (u₀.1 + u) * x) = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x)
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_conj_k h₀ hU _ hE hT u₀.2]
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_dom_k L.sd h' h'₀ _ (GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_j_leftInv_k L hf z x)) T' 1
end PositivityTheory.SiegelWeilFormula.Act
end
end
