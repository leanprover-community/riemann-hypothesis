module

public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

def faceOf3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : DefSub A3.fam3.amb3 → DefFace A3.fam3.base3 :=
  fun Zs => ⟨A3.side3 P0 ψ0 Zs, A3.side3 P1 ψ1 Zs, Dc Zs, Sp Zs, Zsc Zs⟩

def crdOf3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : Crd A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) where
  toR Zs b t := match b with
    | false => (A3.A.fam.R t).toF (A3.A.fam.lvl P0 ψ0) (Zs.Z t)
    | true => (A3.A.fam.R t).toF (A3.A.fam.lvl P1 ψ1) (Zs.Z t)
  toL Zs b j t := match b with
    | false => (A3.A.fam.L j t).toF (A3.A.fam.lvlA P0 ψ0) (Zs.Zl j t)
    | true => (A3.A.fam.L j t).toF (A3.A.fam.lvlA P1 ψ1) (Zs.Zl j t)

end Formalism.IndefR.Cx
