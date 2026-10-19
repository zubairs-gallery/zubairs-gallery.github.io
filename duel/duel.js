/*
 * Reads a Lagoon Block duel link fragment in the browser. Plain ES5, no modules, no build step.
 * Mirrors src/duel/codec.ts (decodeDuel, encodeCode); src/duel/siteDecoder.test.ts keeps them in step.
 * The fragment never leaves the browser: nothing here makes a network request.
 */
(function (root) {
  'use strict';

  var ALPHABET = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_';
  var CROCKFORD = '0123456789ABCDEFGHJKMNPQRSTVWXYZ';
  var MAX_NAME_BYTES = 48;
  var MAX_MOVES = 2000;
  var MOVE_BYTE_MAX = 191;
  var MAX_CODE_SCORE = 1048575;

  // 32-bit multiply without Math.imul.
  function mul32(a, b) {
    var ah = (a >>> 16) & 0xffff;
    var al = a & 0xffff;
    var bh = (b >>> 16) & 0xffff;
    var bl = b & 0xffff;
    return (al * bl + (((ah * bl + al * bh) & 0xffff) << 16)) >>> 0;
  }

  // FNV-1a 32 over bytes[from, to).
  function fnv1a32(bytes, from, to) {
    var h = 0x811c9dc5;
    for (var i = from; i < to; i++) {
      h = mul32((h ^ bytes[i]) >>> 0, 0x01000193);
    }
    return h >>> 0;
  }

  // Base64url without padding; null on any other character or an impossible length.
  function fromBase64url(s) {
    if (typeof s !== 'string' || s.length % 4 === 1) return null;
    var values = [];
    for (var i = 0; i < s.length; i++) {
      var v = ALPHABET.indexOf(s.charAt(i));
      if (v < 0) return null;
      values.push(v);
    }
    var out = [];
    for (var j = 0; j < values.length; j += 4) {
      var n = (values[j] << 18) | ((values[j + 1] || 0) << 12) | ((values[j + 2] || 0) << 6) | (values[j + 3] || 0);
      out.push((n >> 16) & 255);
      if (j + 2 < values.length) out.push((n >> 8) & 255);
      if (j + 3 < values.length) out.push(n & 255);
    }
    return out;
  }

  // Strict UTF-8 decode of bytes[from, to); null when invalid (overlong, surrogate, truncated).
  function utf8Decode(bytes, from, to) {
    var s = '';
    var i = from;
    while (i < to) {
      var b = bytes[i++];
      var cp;
      var extra;
      var min;
      if (b < 0x80) {
        cp = b;
        extra = 0;
        min = 0;
      } else if (b >= 0xc2 && b <= 0xdf) {
        cp = b & 0x1f;
        extra = 1;
        min = 0x80;
      } else if (b >= 0xe0 && b <= 0xef) {
        cp = b & 0x0f;
        extra = 2;
        min = 0x800;
      } else if (b >= 0xf0 && b <= 0xf4) {
        cp = b & 0x07;
        extra = 3;
        min = 0x10000;
      } else {
        return null;
      }
      if (i + extra > to) return null;
      for (var k = 0; k < extra; k++) {
        var c = bytes[i++];
        if ((c & 0xc0) !== 0x80) return null;
        cp = (cp << 6) | (c & 0x3f);
      }
      if (cp < min || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return null;
      if (cp >= 0x10000) {
        cp -= 0x10000;
        s += String.fromCharCode(0xd800 + (cp >> 10), 0xdc00 + (cp & 0x3ff));
      } else {
        s += String.fromCharCode(cp);
      }
    }
    return s;
  }

  // Bounds-checked big-endian reader. Every read returns null past `end`.
  function Reader(bytes, end) {
    this.b = bytes;
    this.end = end;
    this.pos = 0;
  }
  Reader.prototype.u8 = function () {
    return this.pos < this.end ? this.b[this.pos++] : null;
  };
  Reader.prototype.u16 = function () {
    var hi = this.u8();
    var lo = this.u8();
    return hi === null || lo === null ? null : hi * 256 + lo;
  };
  Reader.prototype.u32 = function () {
    var hi = this.u16();
    var lo = this.u16();
    return hi === null || lo === null ? null : hi * 65536 + lo;
  };

  // One player: name, score and move list. Returns {name, score} or null.
  function readSide(r) {
    var nameLen = r.u8();
    if (nameLen === null || nameLen > MAX_NAME_BYTES || r.pos + nameLen > r.end) return null;
    var name = utf8Decode(r.b, r.pos, r.pos + nameLen);
    if (name === null) return null;
    r.pos += nameLen;
    var score = r.u32();
    var count = r.u16();
    if (score === null || count === null || count > MAX_MOVES || r.pos + count > r.end) return null;
    for (var i = 0; i < count; i++) {
      if (r.b[r.pos + i] > MOVE_BYTE_MAX) return null;
    }
    r.pos += count;
    return { name: name, score: score };
  }

  // The short code LB-XXXX-XXXX-XXXX: seed (32), score (20, capped), rulesVersion (4), check (4) as 60 bits.
  function buildCode(seed, score, rulesVersion) {
    var capped = Math.min(score, MAX_CODE_SCORE);
    var tail = capped * 16 + rulesVersion; // 24 bits
    var body = [
      (seed >>> 24) & 255,
      (seed >>> 16) & 255,
      (seed >>> 8) & 255,
      seed & 255,
      (tail >>> 16) & 255,
      (tail >>> 8) & 255,
      tail & 255
    ];
    var bits = [];
    var i;
    var k;
    for (i = 0; i < body.length; i++) {
      for (k = 7; k >= 0; k--) bits.push((body[i] >> k) & 1);
    }
    var check = fnv1a32(body, 0, body.length) & 0xf;
    for (k = 3; k >= 0; k--) bits.push((check >> k) & 1);
    var digits = '';
    for (i = 0; i < 60; i += 5) {
      digits += CROCKFORD.charAt((bits[i] << 4) | (bits[i + 1] << 3) | (bits[i + 2] << 2) | (bits[i + 3] << 1) | bits[i + 4]);
    }
    return 'LB-' + digits.slice(0, 4) + '-' + digits.slice(4, 8) + '-' + digits.slice(8, 12);
  }

  /*
   * hash is location.hash, for example "#d=AQEA...". Returns { name, score, code } or null; never throws.
   * For a challenge link that is the challenger; for a reply link it is the player who sent the reply.
   */
  function readChallenge(hash) {
    try {
      if (typeof hash !== 'string') return null;
      var text = hash.charAt(0) === '#' ? hash.slice(1) : hash;
      if (text.slice(0, 2) !== 'd=') return null;
      var bytes = fromBase64url(text.slice(2));
      if (!bytes || bytes.length < 4) return null;
      var bodyEnd = bytes.length - 4;
      var stored = bytes[bodyEnd] * 16777216 + (bytes[bodyEnd + 1] << 16) + (bytes[bodyEnd + 2] << 8) + bytes[bodyEnd + 3];
      if (fnv1a32(bytes, 0, bodyEnd) !== stored) return null;
      var r = new Reader(bytes, bodyEnd);
      var format = r.u8();
      var rulesVersion = r.u8();
      var kind = r.u8();
      var seed = r.u32();
      if (format !== 1 || rulesVersion === null || seed === null || (kind !== 0 && kind !== 1)) return null;
      var sender = readSide(r);
      if (!sender) return null;
      if (kind === 1) {
        sender = readSide(r);
        if (!sender) return null;
      }
      if (r.pos !== r.end) return null;
      return { name: sender.name, score: sender.score, code: buildCode(seed, sender.score, rulesVersion) };
    } catch (e) {
      return null;
    }
  }

  var api = { readChallenge: readChallenge };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  if (root) root.LagoonDuel = api;
})(typeof window !== 'undefined' ? window : null);
