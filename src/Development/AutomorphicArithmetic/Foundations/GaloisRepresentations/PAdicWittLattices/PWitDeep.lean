module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitDeep :
    KNBasic → GenSm → TransDeep → WitComp → WitForget → WitDeep := by
  intro _ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI
  obtain ⟨k, hk, hAk, hex⟩ := hTD p D G L R gb h hI
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'
    · exact hpos
  let Nk : Lv p := ⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul_left N.2.2 hk⟩
  let M : Lv p := ⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N'.2.2 Nk.2.2⟩
  have hNkM : (↑Nk : ℕ) ∣ ↑M := Dvd.intro_left _ rfl
  refine ⟨M, Dvd.intro _ rfl, ?_, ?_⟩
  · intro u hu
    exact hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)
  · haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1
    haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s
    obtain ⟨o, ψ, ht⟩ := hex N (X Nk).X (X Nk).s (X Nk).univ
    obtain ⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩ := (X N).rep (X Nk).X (X Nk).s o
    have w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ) := ⟨hπ, o, ψ, φ, ht, rfl⟩
    obtain ⟨c, Φc, w₁, -⟩ := hWF p D G L R gb Nk M hNkM (X Nk) (X M)
    have := (hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂
    rw [_root_.mul_one] at this
    exact ⟨_, _, this⟩
