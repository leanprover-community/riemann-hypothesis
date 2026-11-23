module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolOrdV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ¬ TypAt X v →
    localVolumeUnit X ψ v / ZZX X u u' ψ v =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))

def VolTypV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → ∀ v : PlX X, TypAt X v → localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))

def OmV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    (omAt X.B.I.cm.sig X.B.I.J ψ v ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
        Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) *
        aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')

def CondAll : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

def DiffProd : Prop :=
  HasProd (fun v : PlX X => absV v (dV v)) (|(NumberField.discr X.B.I.F : ℝ)|⁻¹)

end Loc

end Formalism.L2.SG.Pf.NcVal
