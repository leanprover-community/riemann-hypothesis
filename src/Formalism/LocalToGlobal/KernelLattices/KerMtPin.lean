module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
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

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def twMt (D : D7) (ξ : D.Dt →* ℂˣ) : ℕ → D.Dt →* ℂˣ := fun j =>
  if 1 ≤ j ∧ j ≤ D.R.m then D.muTil j * ξ else D.muTil j

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.IsUnitNormOneQuotient {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) : Prop :=
  Function.Surjective q ∧
  ∀ (k : t.X.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (t.seam.iE (k : t.X.E)) = t.seam.iE (k : t.X.E) →
    q (ratId t.X.F t.X.E k) = D.e1Dt z

def KerEntTied.XiTil {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (μ : D.what₂.Tup)
    (ξ : D.Dt →* ℂˣ) : Prop :=
  ∀ x, ξ (q x) = Units.map t.seam.σ₀.toMonoidHom ((t.tup μ : Chr t.X.F t.X.E t.X.K) x)

def KerEntTied.MtTwAt {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (P : D.what₂.Tup → Prop) : Prop :=
  ∀ μ, μ ≠ D.what₂.mu0 → P μ → ∃ ξ : D.Dt →* ℂˣ, t.XiTil q μ ξ ∧ ∀ u, (t.O u μ).mt = twMt D ξ

def KerEntTied.MtTwOn {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (P : D.what₂.Tup → Prop) : Prop :=
  ∃ q : (AfE t.X.F t.X.E)ˣ →* D.Dt, t.IsUnitNormOneQuotient q ∧ t.MtTwAt q P

def KerEntTied.MtTwTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop := t.MtTwOn fun _ => True

end Comparison₂

end Formalism.L2.Ker
