module

public import Mathlib

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace Formalism.TwoAdicCyclotomicDecomposition

abbrev GalL (n : ℕ) : Type := (ZMod (2 ^ n))ˣ × ℤˣ × ℤˣ

def JJ (n : ℕ) : GalL n := (-1, -1, -1)

def D2 (n : ℕ) : Subgroup (GalL n) :=
  ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ))).ker

def I2 (n : ℕ) : Subgroup (GalL n) := (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ)).ker

def Iq (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, -1, 1) : GalL n)

def Id (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, 1, -1) : GalL n)

def u5 (n : ℕ) : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right n (by norm_num))

end Formalism.TwoAdicCyclotomicDecomposition
