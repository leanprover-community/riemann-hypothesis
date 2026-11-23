module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel


noncomputable section
namespace GlobalTheory.Fam.PenLoc

theorem psiAt_one_eq {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ S₁ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S₁) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu))
    (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu)
    (P' : Formalism.L2.Col.rowSG Pr sel mu') (hPP : P.1 = P'.1) (hmem : P.1 ∈ Pr.vGs) (hsh : cst.sharp = cst'.sharp)
    (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))) :
    Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y = Formalism.L2.Col.PsiAt Ch sel mu' cst' s P' 1 x y := by
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold Formalism.L2.Col.PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one]
  unfold Formalism.L2.Col.PhiAt
  rw [if_pos hmem, if_pos hmem', hsh, hPP]

theorem lastStepPoints_sub_integral_of_uniformiser_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S S' : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (h : valuation k (((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k)) ≤ 1) (r : GlobalTheory.StepData.XIx (Fin κ) t (s + 1)) :
    S.y0 t r - S'.y0 t r ∈ 𝒪[k] := by
  unfold GlobalTheory.SymChain.SymData.y0
  by_cases hr : r = Sum.inl (Sum.inr 0)
  · subst hr
    simp only [Pi.single_eq_same]
    have h3 := neg_mem (show ((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k) ∈ 𝒪[k] from h)
    rwa [neg_sub] at h3
  · simp [Pi.single_eq_of_ne hr]

end GlobalTheory.Fam.PenLoc
end
