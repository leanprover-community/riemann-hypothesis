module

public import Formalism.LocalToGlobal.InertKernelTheory.FinalA
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.EndInt
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PhNorm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

theorem inert_facts_first_hold : FactsA :=
  ⟨Sigma.invAlg', Sigma.secondEisensteinAlgebraic, endomorphisms_integral_inert, phi_norm_inert_prime⟩

theorem admissible_second_inert (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm2c D X Y :=
  admissible_second_of_facts inert_facts_first_hold D cc δ p g hLT hAt h5 hin hW X Y hY

theorem admissible_eleventh_inert (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X Y :=
  admissible_eleventh_of_facts inert_facts_first_hold D cc δ p g hLT hAt h5 hin hW X Y hY

end Formalism.L2.KerInert
