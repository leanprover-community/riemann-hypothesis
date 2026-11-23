module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.RunFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace RunFrame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

abbrev κ : Type := ∀ w : F.d.P, F.d.kap w

abbrev B (i : F₀.C.ι) : Block E := (F₀.A i).blk F.κ

def ψ (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) : Matrix F.κ F.κ (Hf E (F₀.C.a i) (n - F₀.C.a i) → ℂ) :=
  fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) L

def ptL (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) : PT (F.B i) :=
  (F₀.A i).pt (fun _ => []) (fun _ => []) (F.ψ i L) (sizeOf (F.ψ i L))

def t₀ (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.eL _)

def β (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.betaL _ (F₀.C.le i))

def t₁ (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.fixL _)

def t₂ (i : F₀.C.ι) : PT (F.B i) :=
  (F₀.A i).pt (fun _ => []) (fun _ => []) (rt (F₀.u₁ _) (F₀.u₂ _) (F.ψ i (F.d.eL _)))
    (sizeOf (rt (F₀.u₁ _) (F₀.u₂ _) (F.ψ i (F.d.eL _))))

abbrev Γ : Type := Unit ⊕ (F₀.C.ι × InfinitePlace E × Bool × ℕ × Bool) ⊕ ({w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool)

def dval (_ : RunFrame F₀ T) (x : F₀.C.ι × InfinitePlace E × Bool × ℕ × Bool) : ℂ :=
  if x.2.2.2.2 then zVal [(x.2.2.1, x.2.2.2.1)] ((F₀.A x.1).χb x.2.1) else zVal [(x.2.2.1, x.2.2.2.1)] ((F₀.A x.1).χa x.2.1)

def tD (i : F₀.C.ι) (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool) : PT (F.B i) :=
  (F₀.A i).pt (fun v' => if v' = v ∧ side = false then [(s, m)] else []) (fun v' => if v' = v ∧ side = true then [(s, m)] else [])
    (F.ψ i (F.d.eL _)) (sizeOf (F.ψ i (F.d.eL _)))

def g : F.Γ → ∀ i, BGen (F.B i)
  | .inl _, i => .inr (F.t₀ i)
  | .inr (.inl x), i => if i = x.1 then .inr (F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) else .inl (F.dval x)
  | .inr (.inr x), i => .inr (F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2))

def ug : F.Γ → U.UGen E n
  | .inl _ => .inl 1
  | .inr (.inl x) => .inl (F.dval x)
  | .inr (.inr x) => .inr ⟨x.1.1, F.d.hU x.1.1 x.2.1⟩



instance instIPS_FB (i : F₀.C.ι) : InnerProductSpace ℂ (F.B i).Hb := inferInstance
instance instCS_FB (i : F₀.C.ι) : CompleteSpace (F.B i).Hb := inferInstance

structure Struct : Prop where
  ok : ∀ x i, (F.g x i).Ok
  βok : ∀ i, (F.β i).Ok
  tok : ∀ i, (F.t₁ i).Ok ∧ (F.t₂ i).Ok
  comm : ∀ x y i, Commute (F.g x i).op (F.g y i).op
  commStar : ∀ x y i, Commute (F.g x i).op (star (F.g y i).op)
  βcomm : ∀ i x, Commute (F.β i).op (F.g x i).op ∧ Commute (F.β i).op (star (F.g x i).op)




def toGenIn (hD : DiagAlg) (h : F.Struct) : GenIn π S T F₀.K F₀.W where
  ι := F₀.C.ι
  B := F.B
  I := F.fam.ι
  d := F.R.d
  blk := F.R.blk
  Γ := F.Γ
  g := F.g
  c := fun x => (F.ug x).p F.fam
  β := F.β
  m := F.m
  u := F.R.u
  v := F.v
  i₀ := F.i₀
  a₀ := .inl ()
  ok := h.ok
  βok := h.βok
  comm := h.comm
  commStar := h.commStar
  βcomm := h.βcomm
  ucomm := fun x => F.R.u_comm hD (F.ug x)
  v_ne := F.v_ne
  uv := F.uv
  vblk := fun x => ⟨F.vblk _, by rw [(hD _ _ F.R.blk _ 0 0).2.2.2, F.vblk]; rfl⟩
  a₀ne := one_ne_zero

end RunFrame

end PositivityTheory.Rg.BcB.F

end
