module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorsRationalFormsCommute
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeOperatorsRationalForms_commute : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P k' P', HkIdx i k P → HkIdx i k' P' →
      GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) *
                   GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) =
        GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) *
          GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) ∧
      ∀ g : S.G, GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) * rhoKG S j (Y.rho j h1 h2) g =
        rhoKG S j (Y.rho j h1 h2) g * GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) := by
  first | exact @GlobalTheory.HkKs.opK_comm | exact GlobalTheory.HkKs.opK_comm | (intros; apply GlobalTheory.HkKs.opK_comm <;> assumption)
