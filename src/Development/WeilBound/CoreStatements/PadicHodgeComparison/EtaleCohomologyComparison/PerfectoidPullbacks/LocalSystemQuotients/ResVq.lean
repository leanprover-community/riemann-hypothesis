module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG

section Sub

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)

abbrev stF (m : ℕ) (𝒱 : Set X.Opens) : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m)) :=
  St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT 𝒱

abbrev ιS (m : ℕ) (𝒱 : Set X.Opens) : (stF q ρ m 𝒱).FullSubcategory ⥤ (fl l (B.schFn q) ρ m).FullSubcategory :=
  ObjectProperty.ιOfLE fun _ h => h.1

abbrev sV (m : ℕ) (𝒱 : Set X.Opens) : PDF (WittVector l k) (stF q ρ m 𝒱).FullSubcategory :=
  (thW l (B.schFn q) ρ m).res (stF q ρ m 𝒱).ι

def resV (m : ℕ) (𝒱 : Set X.Opens) :
    CH.Mor (CH.modF (sW l (B.schFn q) ρ m).A) (CH.modF (sV q ρ m 𝒱).A) (RingHom.id (WittVector l k)) where
  G := ιS q ρ m 𝒱
  τ _ := LinearMap.id
  nat _ _ := rfl

def resVq (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k) :
    CH.Mor (sq (IdF.top (sW l (B.schFn q) ρ m).A) (IdF.span (sW l (B.schFn q) ρ m).A c))
      (sq (IdF.top (sV q ρ m 𝒱).A) (IdF.span (sV q ρ m 𝒱).A c)) (RingHom.id (WittVector l k)) where
  G := ιS q ρ m 𝒱
  τ _ := LinearMap.id
  nat _ _ := rfl

end Sub

section Gen

variable {R : Type} [CommRing R] {D D' : Type 1} [Category.{0} D] [Category.{0} D'] {Θ : PDF R D} {Θ' : PDF R D'}
  {P : ObjectProperty D} {P' : ObjectProperty D'}

def subQ {c : R} (m : QMor (Θ.res P.ι) (Θ'.res P'.ι) (IdF.span _ c)) (Q : ObjectProperty D) (Q' : ObjectProperty D')
    (hQ' : Q' ≤ P') (hG : ∀ T : Q'.FullSubcategory, Q (m.G.obj ⟨T.obj, hQ' _ T.property⟩).obj) :
    QMor (Θ.res Q.ι) (Θ'.res Q'.ι) (IdF.span _ c) where
  G := Q.lift (ObjectProperty.ιOfLE hQ' ⋙ m.G ⋙ P.ι) hG
  ρ T := m.ρ ⟨T.obj, hQ' _ T.property⟩
  inj _ := m.inj _
  nat φ x y h := m.nat ((ObjectProperty.ιOfLE hQ').map φ) x y h
  dp _ k x y hx hy h := m.dp _ k x y hx hy h

end Gen

end CrystallineSemistableComparison.Pb.SubquotientResolution

end
