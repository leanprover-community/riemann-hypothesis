module

public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Formalism.LocalToGlobal.Columns.MtRowFrame
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tensCastR {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

variable {D : D7}

def StdPsi {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (tensCastR hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

def RowRepTie {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar} (rowRep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E n)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V))
    (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  ∀ σ, (rowRep σ).Iso (rowRepR θ (eFT σ))

def RowLocPin {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V D.R.r)
    (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  Formalism.L2.RowLocTied D lp (Formalism.L2.Col.rowFrameOf D (OccRows θ PY M J χ e) eFT)

end Formalism.IndefR.principalLevelFrame

end
