module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

def LocSub : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  AscEmb V π d → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N) (w.adicCompletion E))), π.IsLocComp w σ → IsLocCompGL V w σ' →
    ∃ hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
      ∃ f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr
        (fun i : Fin d => GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd), f ≠ 0

def LocDual : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] (N d : ℕ) (x : GlobalTheory.LocGL.IrrGL (k := k)) (σ' : SmIrr (GL (Fin N) k)), IsUnitarisable x.rep → IsUnitarisable σ'.ρ →
  ∀ (hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor x d i.rev).1 = N)
    (f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr (fun i : Fin d => GlobalTheory.LocGL.spehFactor x d i.rev) hd)), f ≠ 0 →
    ∃ hd' : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N,
      ∃ g : (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd').IntertwiningMap σ'.ρ, Function.Surjective g

def Clause3Asc : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  π.IsUnitary → IsNormalised π → AscEmb V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
    GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

def AscSeed : Prop := AscAll ∧ Clause3Asc

end PositivityTheory.Rg.Rs

end
