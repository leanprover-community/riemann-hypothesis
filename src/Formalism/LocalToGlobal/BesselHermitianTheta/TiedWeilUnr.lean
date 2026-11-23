module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def latVWS (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v ∈ S, evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ L0c D V, ∃ y ∈ L0c D W,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (if V.rank ≤ W.rank then a * star (x i) * y j else a * x i * star (y j))}

def UnramOutside (D : D7) (χ : (AE D)ˣ →* Circle) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D →
    (∀ v ∈ S, Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D (x : AE D)) = 1) →
    χ x = 1

def WeilUnramifiedCondition {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S, UnramOutside D (T.eChr χ) S → UnramOutside D (T.eChr χ') S →
    ∀ k ∈ KsphC V S, ∀ k' ∈ KsphC W S, ∀ Φ : X.Sch V W,
      (∀ u ∈ latVWS V W S, Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) = Wl.evS V W Φ) →
      Wl.om V W χ χ' (k, k') Φ = Φ

end Formalism.L2.Theta

end
