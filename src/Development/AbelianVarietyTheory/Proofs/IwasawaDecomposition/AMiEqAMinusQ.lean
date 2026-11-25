module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.RecordWeightVec

theorem aPl_eq_aPlusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) = DV.aPlusQ D ((i : ℕ) + 1) τ n := by
  have hi := i.2
  have h1 : DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n := by
    unfold DV.sigPar Formalism.L2.NTheta.lamAt
    rfl
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aPl_cast D i τ n hn, DV.aPlusQ_eq, h1, h2]
  push_cast
  ring

theorem aMi_eq_aMinusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (q n c : ℕ) (hq : i + 1 + q = D.R.m)
    (hn : n + c + 1 = q) : (aMi D i (D.R.k + i) q τ n : ℚ) = DV.aMinusQ D ((i : ℕ) + 1) τ c := by
  have hi := i.2
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aMi_cast D i τ q n c hq hn, DV.aMinusQ, dite_eq_left (by omega), h2]
  ring

end GlobalTheory.RecordWeightVec
