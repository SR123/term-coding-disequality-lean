import FlowCost

/-! # Parsing the binary input

An executable parser for the self-delimiting encoding of `EncodingCost.lean`
(`encodeNat`, `encodeList`, `encodePair`, `encodeNode`, `encodeBits`) and of the
general input `encodeInput k g = encodeNat k ++ encodeBitsG g`.

The parser is *prefix-consuming*: it never measures the remaining input
(`readBits` reads exactly the announced number of digit cells and fails as soon
as the input is exhausted, so an enormous announced count cannot cause a long
loop), and it is *canonical*: a natural is accepted only if its digit string is
the one the encoder produces (empty, or with the most significant digit set).
Two facts are proved for every decoder `decodeX`:

* round trip: `decodeX (encX x ++ rest) = some (x, rest)`;
* acceptance: `decodeX l = some (x, rest) → l = encX x ++ rest`.

Hence `decodeInput bs = some (k, g) ↔ bs = encodeInput k g` (`decodeInput_eq_some_iff`):
the parser accepts exactly the canonical encodings, and the bit-string decision
`decideBits` is correct on *every* bit string against the canonical language
`StrictBits` (`decideBits_iff_StrictBits`). -/

namespace DisequalityDispersion.Encoded

variable {α β : Type}

/-! ### Parser combinators -/

/-- Run `f`, then `g` on its result and the remainder. -/
def bindP (f : List Bool → Option (α × List Bool)) (g : α → List Bool → Option (β × List Bool))
    (l : List Bool) : Option (β × List Bool) :=
  match f l with
  | none => none
  | some (a, rest) => g a rest

/-- Return a value without reading. -/
def pureP (b : β) (l : List Bool) : Option (β × List Bool) := some (b, l)

theorem bindP_of_eq {f : List Bool → Option (α × List Bool)}
    {g : α → List Bool → Option (β × List Bool)} {l : List Bool} {a : α} {rest : List Bool}
    (h : f l = some (a, rest)) : bindP f g l = g a rest := by
  simp [bindP, h]

theorem bindP_some {f : List Bool → Option (α × List Bool)}
    {g : α → List Bool → Option (β × List Bool)} {l : List Bool} {b : β} {rest : List Bool}
    (h : bindP f g l = some (b, rest)) :
    ∃ a rest₁, f l = some (a, rest₁) ∧ g a rest₁ = some (b, rest) := by
  unfold bindP at h
  cases hf : f l with
  | none => rw [hf] at h; simp at h
  | some p =>
      obtain ⟨a, rest₁⟩ := p
      rw [hf] at h
      exact ⟨a, rest₁, rfl, h⟩

theorem pureP_some {b b' : β} {l rest : List Bool} (h : pureP b l = some (b', rest)) :
    b' = b ∧ rest = l := by
  simp only [pureP, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-! ### Naturals -/

/-- Little-endian bits to a natural. -/
def fromBits : List Bool → ℕ := List.foldr (fun b n => Nat.bit b n) 0

theorem fromBits_bits (n : ℕ) : fromBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [fromBits, Nat.zero_bits]
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      simp only [fromBits, List.foldr_cons]
      simp only [fromBits] at ih
      rw [ih]

theorem fromBits_cons (b : Bool) (bs : List Bool) : fromBits (b :: bs) = Nat.bit b (fromBits bs) := rfl

theorem fromBits_lt (bs : List Bool) : fromBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [fromBits]
  | cons b bs ih =>
      rw [fromBits_cons, Nat.bit_val, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

/-- Canonical digit strings: empty, or the most significant digit is set. -/
def Canon (bs : List Bool) : Bool :=
  match bs.getLast? with
  | none => true
  | some b => b

theorem canon_nil : Canon [] = true := rfl

theorem canon_cons_cons (a b : Bool) (bs : List Bool) : Canon (a :: b :: bs) = Canon (b :: bs) := by
  simp [Canon, List.getLast?_cons_cons]

theorem canon_singleton (b : Bool) : Canon [b] = b := by simp [Canon]

/-- A nonempty canonical digit string has a positive value. -/
theorem fromBits_pos : ∀ (bs : List Bool), bs ≠ [] → Canon bs = true → 0 < fromBits bs
  | [], h, _ => absurd rfl h
  | [b], _, hc => by
      rw [canon_singleton] at hc
      subst hc
      simp [fromBits, Nat.bit_val]
  | a :: b :: bs, _, hc => by
      rw [canon_cons_cons] at hc
      have := fromBits_pos (b :: bs) (by simp) hc
      rw [fromBits_cons, Nat.bit_val]
      omega

/-- A canonical digit string is the digit string of its value. -/
theorem bits_fromBits : ∀ (bs : List Bool), Canon bs = true → (fromBits bs).bits = bs
  | [], _ => by simp [fromBits, Nat.zero_bits]
  | [b], hc => by
      rw [canon_singleton] at hc
      subst hc
      show (Nat.bit true 0).bits = [true]
      rw [Nat.bits_append_bit 0 true (fun _ => rfl), Nat.zero_bits]
  | a :: b :: bs, hc => by
      rw [canon_cons_cons] at hc
      have ih := bits_fromBits (b :: bs) hc
      have hpos := fromBits_pos (b :: bs) (by simp) hc
      rw [fromBits_cons, Nat.bits_append_bit _ _ (fun h => absurd h (by omega)), ih]

theorem canon_bits (n : ℕ) : Canon n.bits = true := by
  induction n using Nat.binaryRec' with
  | zero => simp [Nat.zero_bits, Canon]
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases hb : n.bits with
      | nil =>
          have : n = 0 := by
            have := Nat.size_eq_bits_len n
            rw [hb] at this
            simp only [List.length_nil] at this
            exact Nat.size_eq_zero.mp this.symm
          rw [canon_singleton]; exact h this
      | cons c cs => rw [canon_cons_cons, ← hb]; exact ih

theorem size_of_canon (bs : List Bool) (hc : Canon bs = true) : (fromBits bs).size = bs.length := by
  rw [← Nat.size_eq_bits_len, bits_fromBits bs hc]

/-- Read exactly `c` cells; fails as soon as the input is exhausted. -/
def readBits : ℕ → List Bool → Option (List Bool × List Bool)
  | 0, l => some ([], l)
  | _ + 1, [] => none
  | c + 1, b :: l =>
      match readBits c l with
      | none => none
      | some (bs, rest) => some (b :: bs, rest)

theorem readBits_append : ∀ (bs rest : List Bool), readBits bs.length (bs ++ rest) = some (bs, rest)
  | [], rest => by simp [readBits]
  | b :: bs, rest => by
      simp only [List.length_cons, List.cons_append, readBits]
      rw [readBits_append bs rest]

theorem readBits_some : ∀ (c : ℕ) (l bs rest : List Bool), readBits c l = some (bs, rest) →
    bs.length = c ∧ l = bs ++ rest
  | 0, l, bs, rest, h => by
      simp only [readBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | c + 1, [], bs, rest, h => by simp [readBits] at h
  | c + 1, b :: l, bs, rest, h => by
      simp only [readBits] at h
      cases hr : readBits c l with
      | none => rw [hr] at h; simp at h
      | some p =>
          obtain ⟨bs', rest'⟩ := p
          rw [hr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := readBits_some c l bs' rest' hr
          simp [h1, h2]

/-- Count the leading ones, skip the zero, read that many digit cells, insist on canonicity. -/
def decodeNatAux : ℕ → List Bool → Option (ℕ × List Bool)
  | c, true :: l => decodeNatAux (c + 1) l
  | c, false :: l =>
      match readBits c l with
      | none => none
      | some (bs, rest) => if Canon bs then some (fromBits bs, rest) else none
  | _, [] => none

def decodeNat (l : List Bool) : Option (ℕ × List Bool) := decodeNatAux 0 l

theorem decodeNatAux_replicate (c : ℕ) : ∀ (s : ℕ) (l : List Bool),
    decodeNatAux c (List.replicate s true ++ l) = decodeNatAux (c + s) l
  | 0, l => by simp
  | s + 1, l => by
      rw [List.replicate_succ, List.cons_append]
      simp only [decodeNatAux]
      rw [decodeNatAux_replicate (c + 1) s l]
      congr 1; omega

theorem decodeNat_encodeNat (n : ℕ) (rest : List Bool) :
    decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  unfold decodeNat encodeNat
  rw [List.append_assoc, decodeNatAux_replicate, List.cons_append]
  simp only [decodeNatAux, Nat.zero_add]
  rw [← Nat.size_eq_bits_len, readBits_append]
  simp only [canon_bits, if_true, fromBits_bits]

/-- Acceptance: a parsed natural came from its canonical encoding (with `c` ones already read). -/
theorem decodeNatAux_some : ∀ (c : ℕ) (l : List Bool) (n : ℕ) (rest : List Bool),
    decodeNatAux c l = some (n, rest) →
      c ≤ n.size ∧ l = List.replicate (n.size - c) true ++ false :: n.bits ++ rest
  | c, [], n, rest, h => by simp [decodeNatAux] at h
  | c, true :: l, n, rest, h => by
      simp only [decodeNatAux] at h
      obtain ⟨h1, h2⟩ := decodeNatAux_some (c + 1) l n rest h
      refine ⟨by omega, ?_⟩
      rw [h2]
      have e : n.size - c = (n.size - (c + 1)) + 1 := by omega
      rw [e, List.replicate_succ, List.cons_append]
      simp
  | c, false :: l, n, rest, h => by
      simp only [decodeNatAux] at h
      cases hr : readBits c l with
      | none => rw [hr] at h; simp at h
      | some p =>
          obtain ⟨bs, rest'⟩ := p
          rw [hr] at h
          dsimp only at h
          split_ifs at h with hc
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hlen, hl⟩ := readBits_some c l bs rest' hr
            rw [size_of_canon bs hc, hlen, bits_fromBits bs hc]
            refine ⟨le_rfl, ?_⟩
            simp [hl]

theorem decodeNat_some (l : List Bool) (n : ℕ) (rest : List Bool)
    (h : decodeNat l = some (n, rest)) : l = encodeNat n ++ rest := by
  obtain ⟨_, h2⟩ := decodeNatAux_some 0 l n rest h
  rw [h2]
  simp [encodeNat]

/-- The bit length of a parsed natural is the number of bits consumed. -/
theorem decodeNat_natC (l : List Bool) (n : ℕ) (rest : List Bool)
    (h : decodeNat l = some (n, rest)) : natC n = l.length - rest.length := by
  rw [decodeNat_some l n rest h, List.length_append, encodeNat_length]
  omega

/-! ### Lists, pairs, nodes -/

/-- Read `n` values with `f`. -/
def decodeN (f : List Bool → Option (α × List Bool)) : ℕ → List Bool → Option (List α × List Bool)
  | 0 => pureP []
  | n + 1 => bindP f (fun a => bindP (decodeN f n) (fun as => pureP (a :: as)))

/-- A length followed by that many values. -/
def decodeList (f : List Bool → Option (α × List Bool)) : List Bool → Option (List α × List Bool) :=
  bindP decodeNat (fun n => decodeN f n)

theorem decodeN_encode (f : List Bool → Option (α × List Bool)) (enc : α → List Bool)
    (hf : ∀ a rest, f (enc a ++ rest) = some (a, rest)) :
    ∀ (l : List α) (rest : List Bool), decodeN f l.length ((l.map enc).flatten ++ rest) =
      some (l, rest)
  | [], rest => by simp [decodeN, pureP]
  | a :: l, rest => by
      simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeN]
      rw [bindP_of_eq (hf a _), bindP_of_eq (decodeN_encode f enc hf l rest)]
      rfl

theorem decodeN_some (f : List Bool → Option (α × List Bool)) (enc : α → List Bool)
    (hf : ∀ l a rest, f l = some (a, rest) → l = enc a ++ rest) :
    ∀ (n : ℕ) (l : List Bool) (as : List α) (rest : List Bool),
      decodeN f n l = some (as, rest) → as.length = n ∧ l = (as.map enc).flatten ++ rest
  | 0, l, as, rest, h => by
      obtain ⟨rfl, rfl⟩ := pureP_some h
      simp
  | n + 1, l, as, rest, h => by
      simp only [decodeN] at h
      obtain ⟨a, l₁, h1, h2⟩ := bindP_some h
      obtain ⟨as', l₂, h3, h4⟩ := bindP_some h2
      obtain ⟨rfl, rfl⟩ := pureP_some h4
      obtain ⟨hlen, hl⟩ := decodeN_some f enc hf n l₁ as' rest h3
      refine ⟨by simp [hlen], ?_⟩
      rw [hf l a l₁ h1, hl]
      simp

theorem decodeList_encodeList (f : List Bool → Option (α × List Bool)) (enc : α → List Bool)
    (hf : ∀ a rest, f (enc a ++ rest) = some (a, rest)) (l : List α) (rest : List Bool) :
    decodeList f (encodeList enc l ++ rest) = some (l, rest) := by
  unfold decodeList encodeList
  rw [List.append_assoc, bindP_of_eq (decodeNat_encodeNat _ _)]
  exact decodeN_encode f enc hf l rest

theorem decodeList_some (f : List Bool → Option (α × List Bool)) (enc : α → List Bool)
    (hf : ∀ l a rest, f l = some (a, rest) → l = enc a ++ rest) (l : List Bool) (as : List α)
    (rest : List Bool) (h : decodeList f l = some (as, rest)) : l = encodeList enc as ++ rest := by
  unfold decodeList at h
  obtain ⟨n, l₁, h1, h2⟩ := bindP_some h
  obtain ⟨hlen, hl⟩ := decodeN_some f enc hf n l₁ as rest h2
  rw [decodeNat_some l n l₁ h1, hl, encodeList, ← hlen]
  simp

def decodePair : List Bool → Option ((ℕ × ℕ) × List Bool) :=
  bindP decodeNat (fun a => bindP decodeNat (fun b => pureP (a, b)))

theorem decodePair_encodePair (p : ℕ × ℕ) (rest : List Bool) :
    decodePair (encodePair p ++ rest) = some (p, rest) := by
  unfold decodePair encodePair
  rw [List.append_assoc, bindP_of_eq (decodeNat_encodeNat _ _), bindP_of_eq (decodeNat_encodeNat _ _)]
  rfl

theorem decodePair_some (l : List Bool) (p : ℕ × ℕ) (rest : List Bool)
    (h : decodePair l = some (p, rest)) : l = encodePair p ++ rest := by
  unfold decodePair at h
  obtain ⟨a, l₁, h1, h2⟩ := bindP_some h
  obtain ⟨b, l₂, h3, h4⟩ := bindP_some h2
  obtain ⟨rfl, rfl⟩ := pureP_some h4
  rw [decodeNat_some l a l₁ h1, decodeNat_some l₁ b rest h3]
  simp [encodePair]

/-- Dispatch on a one-bit tag. -/
def tagP (f0 f1 : List Bool → Option (α × List Bool)) : List Bool → Option (α × List Bool)
  | [] => none
  | false :: l => f0 l
  | true :: l => f1 l

def decodeNode : List Bool → Option (Node × List Bool) :=
  tagP (bindP decodeNat (fun i => pureP (.src i)))
    (bindP decodeNat (fun f => bindP (decodeList decodeNat) (fun args => pureP (.app f args))))

theorem decodeNode_encodeNode (nd : Node) (rest : List Bool) :
    decodeNode (encodeNode nd ++ rest) = some (nd, rest) := by
  cases nd with
  | src i =>
      simp only [encodeNode, List.cons_append, decodeNode, tagP]
      rw [bindP_of_eq (decodeNat_encodeNat _ _)]
      rfl
  | app f args =>
      simp only [encodeNode, List.cons_append, decodeNode, tagP, List.append_assoc]
      rw [bindP_of_eq (decodeNat_encodeNat _ _),
        bindP_of_eq (decodeList_encodeList decodeNat encodeNat decodeNat_encodeNat _ _)]
      rfl

theorem decodeNode_some (l : List Bool) (nd : Node) (rest : List Bool)
    (h : decodeNode l = some (nd, rest)) : l = encodeNode nd ++ rest := by
  cases l with
  | nil => simp [decodeNode, tagP] at h
  | cons b l =>
      cases b with
      | false =>
          simp only [decodeNode, tagP] at h
          obtain ⟨i, l₁, h1, h2⟩ := bindP_some h
          obtain ⟨rfl, rfl⟩ := pureP_some h2
          rw [decodeNat_some l i rest h1]
          simp [encodeNode]
      | true =>
          simp only [decodeNode, tagP] at h
          obtain ⟨f, l₁, h1, h2⟩ := bindP_some h
          obtain ⟨args, l₂, h3, h4⟩ := bindP_some h2
          obtain ⟨rfl, rfl⟩ := pureP_some h4
          rw [decodeNat_some l f l₁ h1, decodeList_some decodeNat encodeNat decodeNat_some l₁ args rest h3]
          simp [encodeNode]

/-! ### Instances and the full input -/

/-- Parse the seven fields of an instance in order. -/
def decodeInstance : List Bool → Option (Instance × List Bool) :=
  bindP (decodeList decodeNat) (fun sources =>
    bindP (decodeList decodePair) (fun symbols =>
      bindP (decodeList decodeNode) (fun nodes =>
        bindP decodeNat (fun x =>
          bindP decodeNat (fun y =>
            bindP decodeNat (fun t =>
              bindP (decodeList decodePair) (fun tests =>
                pureP ⟨sources, symbols, nodes, x, y, t, tests⟩)))))))

theorem decodeInstance_encodeBits (γ : Instance) (rest : List Bool) :
    decodeInstance (encodeBits γ ++ rest) = some (γ, rest) := by
  unfold decodeInstance encodeBits
  simp only [List.append_assoc]
  rw [bindP_of_eq (decodeList_encodeList decodeNat encodeNat decodeNat_encodeNat _ _),
    bindP_of_eq (decodeList_encodeList decodePair encodePair decodePair_encodePair _ _),
    bindP_of_eq (decodeList_encodeList decodeNode encodeNode decodeNode_encodeNode _ _),
    bindP_of_eq (decodeNat_encodeNat _ _), bindP_of_eq (decodeNat_encodeNat _ _),
    bindP_of_eq (decodeNat_encodeNat _ _),
    bindP_of_eq (decodeList_encodeList decodePair encodePair decodePair_encodePair _ _)]
  rfl

theorem decodeInstance_some (l : List Bool) (γ : Instance) (rest : List Bool)
    (h : decodeInstance l = some (γ, rest)) : l = encodeBits γ ++ rest := by
  unfold decodeInstance at h
  obtain ⟨sources, l₁, h1, h⟩ := bindP_some h
  obtain ⟨symbols, l₂, h2, h⟩ := bindP_some h
  obtain ⟨nodes, l₃, h3, h⟩ := bindP_some h
  obtain ⟨x, l₄, h4, h⟩ := bindP_some h
  obtain ⟨y, l₅, h5, h⟩ := bindP_some h
  obtain ⟨t, l₆, h6, h⟩ := bindP_some h
  obtain ⟨tests, l₇, h7, h⟩ := bindP_some h
  obtain ⟨rfl, rfl⟩ := pureP_some h
  rw [decodeList_some decodeNat encodeNat decodeNat_some l sources l₁ h1,
    decodeList_some decodePair encodePair decodePair_some l₁ symbols l₂ h2,
    decodeList_some decodeNode encodeNode decodeNode_some l₂ nodes l₃ h3,
    decodeNat_some l₃ x l₄ h4, decodeNat_some l₄ y l₅ h5, decodeNat_some l₅ t l₆ h6,
    decodeList_some decodePair encodePair decodePair_some l₆ tests rest h7]
  simp [encodeBits]

/-- Parse a general instance: the base instance, then the extra output indices. -/
def decodeG : List Bool → Option (GInstance × List Bool) :=
  bindP decodeInstance (fun base => bindP (decodeList decodeNat) (fun outs => pureP ⟨base, outs⟩))

theorem decodeG_encodeBitsG (g : GInstance) (rest : List Bool) :
    decodeG (encodeBitsG g ++ rest) = some (g, rest) := by
  unfold decodeG encodeBitsG
  rw [List.append_assoc, bindP_of_eq (decodeInstance_encodeBits _ _),
    bindP_of_eq (decodeList_encodeList decodeNat encodeNat decodeNat_encodeNat _ _)]
  rfl

theorem decodeG_some (l : List Bool) (g : GInstance) (rest : List Bool)
    (h : decodeG l = some (g, rest)) : l = encodeBitsG g ++ rest := by
  unfold decodeG at h
  obtain ⟨base, l₁, h1, h⟩ := bindP_some h
  obtain ⟨outs, l₂, h2, h⟩ := bindP_some h
  obtain ⟨rfl, rfl⟩ := pureP_some h
  rw [decodeInstance_some l base l₁ h1,
    decodeList_some decodeNat encodeNat decodeNat_some l₁ outs rest h2]
  simp [encodeBitsG]

/-- Parse `(k, g)`. -/
def decodePair' : List Bool → Option ((ℕ × GInstance) × List Bool) :=
  bindP decodeNat (fun k => bindP decodeG (fun g => pureP (k, g)))

theorem decodePair'_encodeInput (k : ℕ) (g : GInstance) (rest : List Bool) :
    decodePair' (encodeInput k g ++ rest) = some ((k, g), rest) := by
  unfold decodePair' encodeInput
  rw [List.append_assoc, bindP_of_eq (decodeNat_encodeNat _ _), bindP_of_eq (decodeG_encodeBitsG _ _)]
  rfl

theorem decodePair'_some (l : List Bool) (k : ℕ) (g : GInstance) (rest : List Bool)
    (h : decodePair' l = some ((k, g), rest)) : l = encodeInput k g ++ rest := by
  unfold decodePair' at h
  obtain ⟨k', l₁, h1, h⟩ := bindP_some h
  obtain ⟨g', l₂, h2, h⟩ := bindP_some h
  obtain ⟨he, hr⟩ := pureP_some h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  subst hr
  rw [decodeNat_some l k l₁ h1, decodeG_some l₁ g rest h2]
  simp [encodeInput]

/-- Parse the full input `(k, g)`; succeeds only if nothing is left over. -/
def decodeInput (l : List Bool) : Option (ℕ × GInstance) :=
  match decodePair' l with
  | some (kg, []) => some kg
  | _ => none

/-- **Round trip**: the binary input of `(k, g)` parses back to `(k, g)`. -/
theorem decodeInput_encodeInput (k : ℕ) (g : GInstance) :
    decodeInput (encodeInput k g) = some (k, g) := by
  unfold decodeInput
  rw [← List.append_nil (encodeInput k g), decodePair'_encodeInput]

/-- **Acceptance**: only canonical encodings parse. -/
theorem decodeInput_some (bs : List Bool) (k : ℕ) (g : GInstance)
    (h : decodeInput bs = some (k, g)) : bs = encodeInput k g := by
  unfold decodeInput at h
  cases hp : decodePair' bs with
  | none => rw [hp] at h; simp at h
  | some p =>
      obtain ⟨⟨k', g'⟩, rest⟩ := p
      rw [hp] at h
      cases rest with
      | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, hg⟩ := h
          subst hk; subst hg
          simpa using decodePair'_some bs k' g' [] hp
      | cons b rest => simp at h

/-- **The parser accepts exactly the canonical encodings.** -/
theorem decodeInput_eq_some_iff (bs : List Bool) (k : ℕ) (g : GInstance) :
    decodeInput bs = some (k, g) ↔ bs = encodeInput k g :=
  ⟨decodeInput_some bs k g, fun h => h ▸ decodeInput_encodeInput k g⟩

theorem encodeInput_injective (k k' : ℕ) (g g' : GInstance)
    (h : encodeInput k g = encodeInput k' g') : k = k' ∧ g = g' := by
  have := decodeInput_encodeInput k g
  rw [h, decodeInput_encodeInput] at this
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact ⟨this.1.symm, this.2.symm⟩

/-- The encoding is prefix-free: no input is a proper prefix of another. -/
theorem encodeInput_prefix (k k' : ℕ) (g g' : GInstance) (rest : List Bool)
    (h : encodeInput k g ++ rest = encodeInput k' g') : rest = [] := by
  have h1 := decodeInput_encodeInput k' g'
  rw [← h] at h1
  unfold decodeInput at h1
  rw [decodePair'_encodeInput] at h1
  cases rest with
  | nil => rfl
  | cons b rest => simp at h1

/-- Sizes of a parsed input are bounded by the length of the bit string. -/
theorem decodeInput_sizes (bs : List Bool) (k : ℕ) (g : GInstance)
    (h : decodeInput bs = some (k, g)) : natC k + sizeG g = bs.length := by
  rw [decodeInput_some bs k g h, encodeInput_length]

/-! ### The bit-string language and decision -/

/-- The canonical bit-string language of the strict problem at degree `k ≥ 2`. -/
def StrictBits (bs : List Bool) : Prop :=
  ∃ (k : ℕ) (g : GInstance), 2 ≤ k ∧ bs = encodeInput k g ∧ g.Strict k

/-- The decision on the bit string: parse, then decide. -/
def decideBits (l : List Bool) : Bool :=
  match decodeInput l with
  | none => false
  | some (k, g) => g.strictDecideP k

theorem decideBits_encodeInput (k : ℕ) (g : GInstance) :
    decideBits (encodeInput k g) = g.strictDecideP k := by
  unfold decideBits
  rw [decodeInput_encodeInput]

/-- Correctness on encoder-produced inputs, for every degree `k ≥ 2`. -/
theorem decideBits_iff (k : ℕ) (hk : 2 ≤ k) (g : GInstance) :
    decideBits (encodeInput k g) = true ↔ g.Strict k := by
  rw [decideBits_encodeInput]
  exact g.strictDecideP_iff k hk

/-- **Whole-language correctness**: on every bit string, `decideBits` accepts exactly the
canonical language `StrictBits`. -/
theorem decideBits_iff_StrictBits (bs : List Bool) : decideBits bs = true ↔ StrictBits bs := by
  unfold decideBits StrictBits
  cases hd : decodeInput bs with
  | none =>
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro k g _ hbs _
      rw [hbs, decodeInput_encodeInput] at hd
      exact absurd hd (by simp)
  | some p =>
      obtain ⟨k, g⟩ := p
      have hbs := decodeInput_some bs k g hd
      simp only
      constructor
      · intro h
        rcases Nat.lt_or_ge k 2 with hk | hk
        · rw [g.strictDecideP_of_degree_lt k hk] at h; exact absurd h (by decide)
        · exact ⟨k, g, hk, hbs, (g.strictDecideP_iff k hk).mp h⟩
      · rintro ⟨k', g', hk', hbs', hs⟩
        rw [hbs'] at hd
        rw [decodeInput_encodeInput] at hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hk, hg⟩ := hd
        subst hk; subst hg
        exact (g'.strictDecideP_iff k' hk').mpr hs

end DisequalityDispersion.Encoded
