# encoding: ascii-8bit
# Bitcoin Utils and Network Protocol in Ruby.

require 'digest/sha2'
require 'digest/rmd160'
require 'openssl'
require 'securerandom'

module Bitcoin
  # Determine the integer class to use. In older versions of ruby (< 2.4.0) the
  # integer class is called Fixnum. In newer version (>= 2.4.0) Fixnum was
  # deprecated in favor of a unification of Fixnum and BigInteger named Integer.
  # Since this project strivers for backwards-compatability, we determine the
  # appropriate class to use at initialization.
  # 
  # This avoids annoying deprecation warnings on newer versions for ourselves
  # and library consumers.
  Integer =
    if Gem::Version.new(RUBY_VERSION) >= Gem::Version.new('2.4.0')
      Integer
    else
      Fixnum
    end

  autoload :Bech32,     'bitcoin/bech32'
  autoload :Connection, 'bitcoin/connection'
  autoload :Protocol,   'bitcoin/protocol'
  autoload :P,          'bitcoin/protocol'
  autoload :Script,     'bitcoin/script'
  autoload :VERSION,    'bitcoin/version'
  autoload :Key,        'bitcoin/key'
  autoload :ExtKey,     'bitcoin/ext_key'
  autoload :ExtPubkey,  'bitcoin/ext_key'
  autoload :Builder,    'bitcoin/builder'
  autoload :BloomFilter,'bitcoin/bloom_filter'

  autoload :Dogecoin,   'bitcoin/dogecoin'
  autoload :Litecoin,   'bitcoin/litecoin'

  autoload :ContractHash,   'bitcoin/contracthash'

  module Trezor
    autoload :Mnemonic,   'bitcoin/trezor/mnemonic'
  end


  module Util

    def address_version; Bitcoin.network[:address_version]; end
    def version_bytes; address_version.size / 2; end
    def p2sh_version; Bitcoin.network[:p2sh_version]; end

    # hash160 is a 20 bytes (160bits) rmd610-sha256 hexdigest.
    def hash160(hex)
      bytes = [hex].pack("H*")
      Digest::RMD160.hexdigest Digest::SHA256.digest(bytes)
    end

    # checksum is a 4 bytes sha256-sha256 hexdigest.
    def checksum(hex)
      b = [hex].pack("H*") # unpack hex
      Digest::SHA256.hexdigest( Digest::SHA256.digest(b) )[0...8]
    end

    # verify base58 checksum for given +base58+ data.
    def base58_checksum?(base58)
      hex = decode_base58(base58) rescue nil
      return false unless hex
      checksum(hex[0...(version_bytes + 20) * 2]) == hex[-8..-1]
    end
    alias :address_checksum? :base58_checksum?

    # check if given +address+ is valid.
    # this means having a correct version byte, length and checksum.
    def valid_address?(address)
      address_type(address) != nil
    end

    # check if given +pubkey+ is valid.
    def valid_pubkey?(pubkey)
      ::OpenSSL::PKey::EC::Point.from_hex(bitcoin_elliptic_curve.group, pubkey)
      true
    rescue OpenSSL::PKey::EC::Point::Error
      false
    rescue OpenSSL::BNError
      # Occasionally, a malformed value will fail hex decoding completely and
      # instead of raising an `OpenSSL::PKey::EC::Point::Error` will raise this
      # error. We capture this failure mode here as well.
      false
    end

    # get hash160 for given +address+. returns nil if address is invalid.
    def hash160_from_address(address)
      case address_type(address)
      when :witness_v0_keyhash
        _, witness_program_hex = decode_segwit_address(address)
        witness_program_hex
      when :hash160, :p2sh
        start_idx = version_bytes * 2
        stop_idx = start_idx + 40 # 20 bytes (2 chars per byte)
        decode_base58(address)[start_idx...stop_idx]
      end
    end

    # get type of given +address+.
    def address_type(address)
      segwit_decoded = decode_segwit_address(address) rescue nil
      if segwit_decoded
        witness_version, witness_program_hex = segwit_decoded
        witness_program = [witness_program_hex].pack("H*")

        if witness_version == 0 && witness_program.bytesize == 20
          return :witness_v0_keyhash
        end

        if witness_version == 0 && witness_program.bytesize == 32
          return :witness_v0_scripthash
        end
      end

      hex = decode_base58(address) rescue nil

      target_size = (version_bytes + 20 + 4) * 2 # version_bytes + 20 bytes hash + 4 bytes checksum
      if hex && hex.bytesize == target_size && address_checksum?(address)
        # Litecoin updates the P2SH version byte, and this method should recognize both.
        p2sh_versions = [p2sh_version]
        if Bitcoin.network[:legacy_p2sh_versions]
          p2sh_versions += Bitcoin.network[:legacy_p2sh_versions]
        end

        case hex[0...(version_bytes * 2)]
        when address_version
          return :hash160
        when *p2sh_versions
          return :p2sh
        end
      end

      nil
    end

    def sha256(hex)
      Digest::SHA256.hexdigest([hex].pack("H*"))
    end

    def hash160_to_address(hex)
      encode_address hex, address_version
    end

    def hash160_to_p2sh_address(hex)
      encode_address hex, p2sh_version
    end

    def encode_address(hex, version)
      hex = version + hex
      encode_base58(hex + checksum(hex))
    end

    def pubkey_to_address(pubkey)
      hash160_to_address( hash160(pubkey) )
    end

    def pubkeys_to_p2sh_multisig_address(m, *pubkeys)
      redeem_script = Bitcoin::Script.to_p2sh_multisig_script(m, *pubkeys).last
      return Bitcoin.hash160_to_p2sh_address(Bitcoin.hash160(redeem_script.hth)), redeem_script
    end


    def encode_segwit_address(version, program_hex)
      hrp = Bitcoin.network[:bech32_hrp]
      raise "Invalid network" if hrp.nil?

      program = [program_hex].pack("H*")

      return nil if version > 16
      length = program.size
      return nil if version == 0 && length != 20 && length != 32
      return nil if length < 2 || length > 40

      data = [ version ] + Bitcoin::Bech32.convert_bits(program.unpack("C*"), from_bits: 8, to_bits: 5, pad: true)

      address = Bitcoin::Bech32.encode(hrp, data)

      return address.nil? ? nil : address
    end

    def decode_segwit_address(address)
      hrp = Bitcoin.network[:bech32_hrp]
      return nil if hrp.nil?

      actual_hrp, data  = Bitcoin::Bech32.decode(address)

      return nil if actual_hrp.nil?
      length = data.size
      return nil if length == 0 || length > 65
      return nil if hrp != actual_hrp
      return nil if data[0] > 16


      program = Bitcoin::Bech32.convert_bits(data[1..-1], from_bits: 5, to_bits: 8, pad: false)
      return nil if program.nil?

      length = program.size
      return nil if length < 2 || length > 40
      return nil if data[0] == 0 && length != 20 && length != 32

      program_hex = program.pack("C*").unpack("H*").first
      return [data[0], program_hex]
    end

    def int_to_base58(int_val, leading_zero_bytes=0)
      alpha = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
      base58_val, base = '', alpha.size
      while int_val > 0
        int_val, remainder = int_val.divmod(base)
        base58_val = alpha[remainder] + base58_val
      end
      base58_val
    end

    def base58_to_int(base58_val)
      alpha = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
      int_val, base = 0, alpha.size
      base58_val.reverse.each_char.with_index do |char,index|
        raise ArgumentError, 'Value not a valid Base58 String.' unless char_index = alpha.index(char)
        int_val += char_index*(base**index)
      end
      int_val
    end

    def encode_base58(hex)
      leading_zero_bytes  = (hex.match(/^([0]+)/) ? $1 : '').size / 2
      ("1"*leading_zero_bytes) + int_to_base58( hex.to_i(16) )
    end

    def decode_base58(base58_val)
      s = base58_to_int(base58_val).to_s(16); s = (s.bytesize.odd? ? '0'+s : s)
      s = '' if s == '00'
      leading_zero_bytes = (base58_val.match(/^([1]+)/) ? $1 : '').size
      s = ("00"*leading_zero_bytes) + s  if leading_zero_bytes > 0
      s
    end
    alias_method :base58_to_hex, :decode_base58

    # target compact bits (int) to bignum hex
    def decode_compact_bits(bits)
      if Bitcoin.network_project == :dogecoin
        bytes = Array.new(size=((bits >> 24) & 255), 0)
        bytes[0] = (bits >> 16) & 0x7f if size >= 1
        bytes[1] = (bits >>  8) & 255 if size >= 2
        bytes[2] = (bits      ) & 255 if size >= 3
        target = bytes.pack("C*").unpack("H*")[0].rjust(64, '0')
        # Bit number 24 represents the sign
        if (bits & 0x00800000) != 0
          "-" + target
        else
          target
        end
      else
        bytes = Array.new(size=((bits >> 24) & 255), 0)
        bytes[0] = (bits >> 16) & 255 if size >= 1
        bytes[1] = (bits >>  8) & 255 if size >= 2
        bytes[2] = (bits      ) & 255 if size >= 3
        bytes.pack("C*").unpack("H*")[0].rjust(64, '0')
      end
    end

    # target bignum hex to compact bits (int)
    def encode_compact_bits(target)
      bytes = OpenSSL::BN.new(target, 16).to_mpi
      size = bytes.size - 4
      nbits = size << 24
      nbits |= (bytes[4] << 16) if size >= 1
      nbits |= (bytes[5] <<  8) if size >= 2
      nbits |= (bytes[6]      ) if size >= 3
      nbits
    end

    def decode_target(target_bits)
      case target_bits
      when Bitcoin::Integer
        [ decode_compact_bits(target_bits).to_i(16), target_bits ]
      when String
        [ target_bits.to_i(16), encode_compact_bits(target_bits) ]
      end
    end

    def bitcoin_elliptic_curve
      ::OpenSSL::PKey::EC.new("secp256k1")
    end

    def generate_key
      key = bitcoin_elliptic_curve.generate_key
      inspect_key( key )
    end

    def inspect_key(key)
      [ key.private_key_hex, key.public_key_hex ]
    end

    def generate_address
      prvkey, pubkey = generate_key
      [ pubkey_to_address(pubkey), prvkey, pubkey, hash160(pubkey) ]
    end

    def bitcoin_hash(hex)
      Digest::SHA256.digest(
        Digest::SHA256.digest( [hex].pack("H*").reverse )
      ).reverse.bth
    end

    def bitcoin_byte_hash(bytes)
      Digest::SHA256.digest(Digest::SHA256.digest(bytes))
    end

    def bitcoin_mrkl(a, b); bitcoin_hash(b + a); end

    def block_hash(prev_block, mrkl_root, time, bits, nonce, ver)
      h = "%08x%08x%08x%064s%064s%08x" %
            [nonce, bits, time, mrkl_root, prev_block, ver]
      bitcoin_hash(h)
    end

    def litecoin_hash(hex)
      bytes = [hex].pack("H*").reverse
      begin
        require "scrypt" unless defined?(::SCrypt)
        hash = SCrypt::Engine.__sc_crypt(bytes, bytes, 1024, 1, 1, 32)
      rescue LoadError
        hash = Litecoin::Scrypt.scrypt_1024_1_1_256_sp(bytes)
      end
      hash.reverse.unpack("H*")[0]
    end

    def block_scrypt_hash(prev_block, mrkl_root, time, bits, nonce, ver)
      h = "%08x%08x%08x%064s%064s%08x" %
            [nonce, bits, time, mrkl_root, prev_block, ver]
      litecoin_hash(h)
    end

    # get merkle tree for given +tx+ list.
    def hash_mrkl_tree(tx)
      return [nil]  if tx != tx.uniq
      chunks = [ tx.dup ]
      while chunks.last.size >= 2
        chunks << chunks.last.each_slice(2).map {|a, b| bitcoin_mrkl( a, b || a ) }
      end
      chunks.flatten
    end

    # get merkle branch connecting given +target+ to the merkle root of +tx+ list
    def hash_mrkl_branch(tx, target)
      return [ nil ]  if tx != tx.uniq
      branch, chunks = [], [ tx.dup ]
      while chunks.last.size >= 2
        chunks << chunks.last.each_slice(2).map {|a, b|
          hash = bitcoin_mrkl( a, b || a )
          next hash  unless [a, b].include?(target)
          branch << (a == target ? (b || a) : a)
          target = hash
        }
      end
      branch
    end

    # get merkle root from +branch+ and +target+.
    def mrkl_branch_root(branch, target, idx)
      branch.each do |hash|
        a, b = *( idx & 1 == 0 ? [target, hash] : [hash, target] )
        idx >>= 1;
        target = bitcoin_mrkl( a, b )
      end
      target
    end

    def sign_data(key, data)
      sig = nil
      loop {
        sig = key.dsa_sign_asn1(data)
        sig = if Script.is_low_der_signature?(sig)
                sig
              else
                Bitcoin::OpenSSL_EC.signature_to_low_s(sig)
              end

        buf = sig + [Script::SIGHASH_TYPE[:all]].pack("C") # is_der_signature expects sig + sighash_type format
        if Script.is_der_signature?(buf)
          break
        else
          p ["Bitcoin#sign_data: invalid der signature generated, trying again.", data.unpack("H*")[0], sig.unpack("H*")[0]]
        end
      }
      return sig
    end

    def verify_signature(hash, signature, public_key)
      key  = bitcoin_elliptic_curve
      key.public_key = ::OpenSSL::PKey::EC::Point.from_hex(key.group, public_key)
      signature = Bitcoin::OpenSSL_EC.repack_der_signature(signature)
      if signature
        key.dsa_verify_asn1(hash, signature)
      else
        false
      end
    rescue OpenSSL::PKey::ECError, OpenSSL::PKey::EC::Point::Error, OpenSSL::BNError
      false
    end

    def open_key(private_key, public_key=nil)
      key  = bitcoin_elliptic_curve
      key.private_key = ::OpenSSL::BN.from_hex(private_key)
      public_key = regenerate_public_key(private_key) unless public_key
      key.public_key  = ::OpenSSL::PKey::EC::Point.from_hex(key.group, public_key)
      key
    end

    def regenerate_public_key(private_key)
      OpenSSL_EC.regenerate_key(private_key)[1]
    end

    def bitcoin_signed_message_hash(message)
      message = message.dup.force_encoding('binary')

      magic = Bitcoin.network[:message_magic]
      buf = Protocol.pack_var_int(magic.bytesize) + magic
      buf << Protocol.pack_var_int(message.bytesize) + message

      Digest::SHA256.digest(Digest::SHA256.digest(buf))
    end

    def sign_message(private_key_hex, public_key_hex, message)
      hash = bitcoin_signed_message_hash(message)
      signature = OpenSSL_EC.sign_compact(hash, private_key_hex, public_key_hex)
      { 'address' => pubkey_to_address(public_key_hex), 'message' => message, 'signature' => [ signature ].pack("m0") }
    end

    def verify_message(address, signature, message)
      signature = signature.unpack("m0")[0] rescue nil # decode base64
      return false unless valid_address?(address)
      return false unless signature
      return false unless signature.bytesize == 65
      hash = bitcoin_signed_message_hash(message)
      pubkey = OpenSSL_EC.recover_compact(hash, signature)
      pubkey_to_address(pubkey) == address if pubkey
    end

    # block count when the next retarget will take place.
    def block_next_retarget(block_height)
      (block_height + (RETARGET_INTERVAL-block_height.divmod(RETARGET_INTERVAL).last)) - 1
    end

    # current difficulty as a multiple of the minimum difficulty (highest target).
    def block_difficulty(target_nbits)
      # max_target      = 0x00000000ffff0000000000000000000000000000000000000000000000000000
      # current_target  = Bitcoin.decode_compact_bits(target_nbits).to_i(16)
      # "%.7f" % (max_target / current_target.to_f)
      bits, max_body, scaland = target_nbits, Math.log(0x00ffff), Math.log(256)
      "%.7f" % Math.exp(max_body - Math.log(bits&0x00ffffff) + scaland * (0x1d - ((bits&0xff000000)>>24)))
    end

    # Calculate new difficulty target. Note this takes in details of the preceeding
    # block, not the current one.
    #
    # prev_height is the height of the block before the retarget occurs
    # prev_block_time "time" field from the block before the retarget occurs
    # prev_block_bits "bits" field from the block before the retarget occurs (target as a compact value)
    # last_retarget_time is the "time" field from the block when a retarget last occurred
    def block_new_target(prev_height, prev_block_time, prev_block_bits, last_retarget_time)
      # target interval - what is the ideal interval between the blocks
      retarget_time = Bitcoin.network[:retarget_time]

      actual_time = prev_block_time - last_retarget_time

      min = retarget_time / 4
      max = retarget_time * 4

      actual_time = min if actual_time < min
      actual_time = max if actual_time > max

      # It could be a bit confusing: we are adjusting difficulty of the previous block, while logically
      # we should use difficulty of the previous retarget block

      prev_target = decode_compact_bits(prev_block_bits).to_i(16)

      new_target = prev_target * actual_time / retarget_time
      if new_target < Bitcoin.decode_compact_bits(Bitcoin.network[:proof_of_work_limit]).to_i(16)
        encode_compact_bits(new_target.to_s(16))
      else
        Bitcoin.network[:proof_of_work_limit]
      end
    end

    # average number of hashes required to win a block with the current target. (nbits)
    def block_hashes_to_win(target_nbits)
      current_target  = decode_compact_bits(target_nbits).to_i(16)
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff / current_target
    end

    # probability of a single hash solving a block with the current difficulty.
    def block_probability(target_nbits)
      current_target  = decode_compact_bits(target_nbits).to_i(16)
      "%.55f" % (current_target.to_f / 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
    end

    # average time to find a block in seconds with the current target. (nbits)
    def block_average_hashing_time(target_nbits, hashes_per_second)
      block_hashes_to_win(target_nbits) / hashes_per_second
    end

    # average mining time (in days) using Mh/s to get btc
    def block_average_mining_time(block_nbits, block_height, mega_hashes_per_second, target_btc=1.0)
      seconds = block_average_hashing_time(block_nbits, mega_hashes_per_second * 1_000_000)
      reward  = block_creation_reward(block_height) / COIN # satoshis to btc
      (days = seconds / 60 / 60 / 24) * (target_btc / reward)
    end

    # shows the total number of Bitcoins in circulation, reward era and reward in that era.
    def blockchain_total_btc(height)
      reward, interval = Bitcoin.network[:reward_base], Bitcoin.network[:reward_halving]
      total_btc = reward
      reward_era, remainder = (height).divmod(interval)
      reward_era.times{
        total_btc += interval * reward
        reward = reward / 2
      }
      total_btc += remainder * reward
      [total_btc, reward_era+1, reward, height]
    end

    def block_creation_reward(block_height)
      Bitcoin.network[:reward_base] / (2 ** (block_height / Bitcoin.network[:reward_halving].to_f).floor)
    end
  end

  extend Util

  module  BinaryExtensions
    # bin-to-hex
    def bth; unpack("H*")[0]; end
    # hex-to-bin
    def htb; [self].pack("H*"); end

    def htb_reverse; htb.reverse; end
    def hth; unpack("H*")[0]; end
    def reverse_hth; reverse.hth; end
  end

  class ::String
    include Bitcoin::BinaryExtensions
  end


  module ::OpenSSL
    class BN
      def self.from_hex(hex); new(hex, 16); end
      def to_hex; to_i.to_s(16); end
      def to_mpi; to_s(0).unpack("C*"); end
    end
    class PKey::EC
      def private_key_hex; private_key.to_hex.rjust(64, '0'); end
      def public_key_hex;  public_key.to_hex.rjust(130, '0'); end
      def pubkey_compressed?; public_key.group.point_conversion_form == :compressed; end
    end
    class PKey::EC::Point
      def self.from_hex(group, hex)
        new(group, BN.from_hex(hex))
      end
      def to_hex; to_bn.to_hex; end
      def self.bn2mpi(hex) BN.from_hex(hex).to_mpi; end
      def ec_add(point); self.class.new(group, OpenSSL::BN.from_hex(OpenSSL_EC.ec_add(self, point))); end
    end
  end

  autoload :OpenSSL_EC, "bitcoin/ffi/openssl"

  autoload :Secp256k1, "bitcoin/ffi/secp256k1"
  autoload :BitcoinConsensus, "bitcoin/ffi/bitcoinconsensus"

  @network = :bitcoin

  def self.network
    # Store the copy of network options so we can modify them in tests without breaking the defaults
    @network_options ||= NETWORKS[@network].dup
  end

  def self.network_name
    @network ||= nil
  end

  def self.network_project
    @network_project ||= nil
  end

  def self.network=(name)
    raise "Network descriptor '#{name}' not found."  unless NETWORKS[name.to_sym]
    @network_options = nil # clear cached parameters
    @network = name.to_sym
    @network_project = network[:project] rescue nil
    Dogecoin.load  if dogecoin? || dogecoin_testnet?
    Namecoin.load  if namecoin? && defined?(Namecoin)
    @network
  end

  [:bitcoin, :namecoin, :litecoin, :dogecoin, :dogecoin_testnet].each do |n|
    instance_eval "def #{n}?; network_project == :#{n}; end"
  end


  # maximum size of a block (in bytes)
  MAX_BLOCK_SIZE = 1_000_000_000

  # soft limit for new blocks
  MAX_BLOCK_SIZE_GEN = MAX_BLOCK_SIZE/2

  # maximum number of signature operations in a block
  MAX_BLOCK_SIGOPS = MAX_BLOCK_SIZE / 50

  # maximum number of orphan transactions to be kept in memory
  MAX_ORPHAN_TRANSACTIONS = MAX_BLOCK_SIZE/100

  # Threshold for lock_time: below this value it is interpreted as block number, otherwise as UNIX timestamp.
  LOCKTIME_THRESHOLD = 500000000 # Tue Nov  5 00:53:20 1985 UTC

  # maximum integer value
  UINT32_MAX = 0xffffffff
  INT_MAX = 0xffffffff # deprecated name, left here for compatibility with existing users.

  # number of confirmations required before coinbase tx can be spent
  COINBASE_MATURITY = 100

  # interval (in blocks) for difficulty retarget
  RETARGET_INTERVAL = 2016
  RETARGET = 2016 # deprecated constant


  # interval (in blocks) for mining reward reduction
  REWARD_DROP = 210_000

  CENT =   1_000_000
  COIN = 100_000_000

  MIN_FEE_MODE     = [ :block, :relay, :send ]

  NETWORKS = {
    bitcoin: {
      project: :bitcoin,
      magic_head: "\xF1\xCF\xA6\xD3",
      message_magic: "Bitcoin Signed Message:\n",
      address_version: "25",
      p2sh_version: "05",
      privkey_version: "80",
      extended_privkey_version: "0488ADE4",
      extended_pubkey_version: "0488B21E",
      bech32_hrp: "zh",
      default_port: 8333,
      protocol_version: 70001,
      coinbase_maturity: 100,
      reward_base: 50 * COIN,
      reward_halving: 210_000,
      retarget_interval: 2016,
      retarget_time: 1209600, # 2 weeks
      target_spacing: 600, # block interval
      max_money: 21_000_000 * COIN,
      min_tx_fee: 10_000,
      min_relay_tx_fee: 10_000,
      free_tx_bytes: 1_000,
      dust: CENT,
      per_dust_fee: false,
      bip34_height: 227931,
      dns_seeds: [
        "seed.bitcoin.sipa.be",
        "dnsseed.bluematt.me",
        "dnsseed.bitcoin.dashjr.org",
        "bitseed.xf2.org",
        "dnsseed.webbtc.com",
      ],
      genesis_hash: "000007af309bdd818599502f8fc8af0943c4ce302df2298b14e59abd0c38e07b0",
      proof_of_work_limit: 0x1d00ffff,
      known_nodes: [
      ],
      checkpoints: {
      }
    }
  }

  NETWORKS[:testnet] = NETWORKS[:bitcoin].merge({
    })

  NETWORKS[:regtest] = NETWORKS[:testnet].merge({
    })

  NETWORKS[:testnet3] = NETWORKS[:testnet].merge({
    })

  NETWORKS[:litecoin] = NETWORKS[:bitcoin].merge({
    })

  NETWORKS[:litecoin_testnet] = NETWORKS[:litecoin].merge({
    })

  NETWORKS[:dogecoin] = NETWORKS[:litecoin].merge({
    })

  NETWORKS[:dogecoin_testnet] = NETWORKS[:dogecoin].merge({
    })

  NETWORKS[:namecoin] = NETWORKS[:bitcoin].merge({
    })

  NETWORKS[:namecoin_testnet] = NETWORKS[:namecoin].merge({
    })

  NETWORKS[:namecoin_regtest] = NETWORKS[:namecoin_testnet].merge({
    })

end
