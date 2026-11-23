module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar
public import Development.AutomorphicArithmetic.WhittakerHecke.CentralCharGaloisInvariantOfConjInv
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

@[expose] public section

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.cenEx_of :
    CenEx := by
  intro E _ _ _ hE P hP
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar (GlobalTheory.CuspRep.CG.mk P)
  obtain ⟨χ, hχ⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.A.normChar_of_inv hE ω (UpperTheory.centralChar_galois_invariant_of_conjInv E P ω hω hP)
  refine ⟨χ, fun f hf z g => ?_⟩
  have h1 := (GlobalTheory.CuspRep.CuspSub.hasCentral_iff (π := P) (ω := ω)).2 hω z f hf
  have h2 := congrFun (congrArg Subtype.val h1) g
  rw [GlobalTheory.CuspRep.scalar_comm, ← hχ z]
  exact h2
