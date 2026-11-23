module

public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Joints

variable (D : D7)

def finE : Formalism.L2.Theta.AE D →+* D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).toRingHom.comp (Formalism.L2.Theta.finPart D)

def IsRatioAt (e : Formalism.L2.Theta.AE D) (k : D.host.E) (y : Formalism.L2.Theta.AE D) : Prop :=
  y * Formalism.L2.Theta.cA D (Formalism.L2.JoinChr.locE D e k) = Formalism.L2.JoinChr.locE D e k

def InPrimeK (x : D.host.E) (p : HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∃ y : 𝓞 D.host.K, ((y : D.host.K) : D.host.E) = x ∧ y ∈ p.asIdeal


open Classical in
def redV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : Formalism.L2.Forms.kv F v :=
  if h : x ∈ v.adicCompletionIntegers F then IsLocalRing.residue (v.adicCompletionIntegers F) ⟨x, h⟩ else 0

end Formalism.L2.Joints

end
