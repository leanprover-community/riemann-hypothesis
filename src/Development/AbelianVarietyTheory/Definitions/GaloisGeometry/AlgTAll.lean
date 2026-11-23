module

public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAllOfJetMomR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.ThLoc.Alg

theorem algTAll : Formalism.L2.KerInert.AlgTAll := by
  intro D cc δ B χ hcc hδ hχ N N' L L' hA t ht α
  have hC : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hT := GlobalTheory.Mem.Col2.JetAlgebraic.ta_thMoved B hC hA.2.2.1 hA.2.2.2
  have h := (GlobalTheory.Mem.Col2.JetAlgebraic.TA.comb (cc := cc) (δ := δ) (Finset.univ : Finset Unit)
    (fun _ => Base.chiFac χ N N' L L') (fun _ => B.thMoved N N' L L')
    (fun _ => GlobalTheory.MomT.FromComb.chiFac_mem hχ hA) (fun _ => hT)).2
  have e : (fun z => ∑ _a ∈ (Finset.univ : Finset Unit), Base.chiFac χ N N' L L' * B.thMoved N N' L L' z) =
      B.eNat χ N N' L L' := by
    funext z
    simp [Base.eNat]
  rw [e] at h
  obtain ⟨a, ha, hat⟩ := ht
  exact h t (GlobalTheory.ThetaAlgebraic.sat_of_nsmul ha
    (GlobalTheory.Mem.Col2.JetAlgebraic.la_le_sat hC hA.2.2.1 hA.2.2.2 hat)) α

end GlobalTheory.ThLoc.Alg
