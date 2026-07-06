using DataStructures
using ProgressMeter

const MAX_LEN = 31
const Word = NTuple{MAX_LEN + 1, UInt8}

function encode_word(vec::Vector{Int})::Word
    L = length(vec)
    @assert L <= MAX_LEN "The string exceeds MAX_LEN($MAX_LEN)."
    return ntuple(i -> (i == 1 ? UInt8(L) : (i-1 <= L ? UInt8(vec[i-1]) : 0x00)), Val(MAX_LEN + 1))
end

function get_next_states!(next_states::Set{Word}, w::Word, allow_same_char::Bool)
    L = Int(w[1])
    if L < 2
        return
    end
    
    if L + 1 <= MAX_LEN
        for i in 1:L-1
            # w[2] から w[L+1] が実際の文字データ
            # 隣り合うペアは w[i+1] と w[i+2]
            x = w[i+1]
            y = w[i+2]
            if !allow_same_char && x == y
                continue
            end
            
            # nxtの長さはw.len+1になる
            # nxtの2~iまではwと同じ
            # nxt[i+1]はyに、nxt[i+2]=nxt[i+3]=xになる
            # nxtのi+4~L+2までは、wのi+3~L+1までになる
            # nxtのL+3~は0
            nxt = ntuple(Val(MAX_LEN + 1)) do j
                if j <= i
                    if j == 1
                        return UInt8(L+1)
                    else
                        return w[j]
                    end
                elseif j >= L+3
                    return 0x00
                elseif j >= i+4
                    return w[j-1]
                elseif j >= i+2
                    return x
                elseif j == i+1
                    return y
                else
                    return UInt8(L+1)
                end
            end

            push!(next_states, nxt)
        end
    end
    
    for i in 1:L-2
        # 3文字の並びは w[i+1], w[i+2], w[i+3]
        y = w[i+1]
        x = w[i+2]
        
        if x == w[i+3]
            if !allow_same_char && y == x
                continue
            end
            
            # nxtの長さはw.len-1になる
            # nxtの2~iまではwと同じ
            # nxt[i+1]=xに、nxt[i+2]=yになる
            # nxtのi+3~Lまではwのi+4~L+1までになる
            # nxtのL+1~は0
            nxt = ntuple(Val(MAX_LEN + 1)) do j
                if j <= i
                    if j == 1
                        return UInt8(L-1)
                    else
                        return w[j]
                    end
                elseif j >= L+1
                    return 0x00
                elseif j >= i+3
                    return w[j+1]
                elseif j == i+1
                    return x
                else
                    return y
                end
            end
            push!(next_states, nxt)
        end
    end
end

function bidirectional_bfs_quiet(start_str::String, target_str::String; allow_same_char::Bool=true, max_depth::Int=30, max_length::Int=15)::Int
        if start_str == target_str
        return 0
    elseif length(start_str) <= 1 || length(target_str) <= 1
        return -1
    end

    start_set = Set(start_str)
    target_set = Set(target_str)
    if start_set != target_set
        return -1
    end

    all_chars = unique(start_str)
    char_to_id = Dict(c => i for (i, c) in enumerate(all_chars))

    start_word  = encode_word([char_to_id[c] for c in start_str])
    target_word = encode_word([char_to_id[c] for c in target_str])

    forward_visited  = Set{Word}([start_word])
    backward_visited = Set{Word}([target_word])

    # 探索の最前線にいるノードの集合
    forward_layer  = Set{Word}([start_word])
    backward_layer = Set{Word}([target_word])
    # 一時置き場
    # next_layer_buf: 「階層全体（世代全体）」 の次の最前線ノードをすべて集める大きな器。
    # local_transitions: 「今処理しているノード1個だけ」 から派生する遷移先を、アロケーションフリーで一時的に計算するための小さな作業机。
    next_layer_buf = Set{Word}()
    local_transitions = Set{Word}()

    found = false
    collision_node = start_word
    step = 0

    for _ in 1:max_depth
        step += 1
        if isempty(forward_layer) || isempty(backward_layer)
            break
        end

        empty!(next_layer_buf)

        if length(forward_layer) <= length(backward_layer)
            # forwardが短いので、そちらを展開する
            for curr in forward_layer
                
                empty!(local_transitions)
                get_next_states!(local_transitions, curr, allow_same_char)
                # local_transitionsにcurrから行けるやつが全て入った

                for nxt in local_transitions
                    
                    if nxt[1] > max_length
                        continue
                    end

                    if nxt ∈ backward_visited
                        push!(forward_visited, nxt)
                        collision_node = nxt
                        found = true
                        break
                    end

                    if nxt ∉ forward_visited
                        push!(forward_visited,nxt)     # 根へ向いた矢印をつける nxt→curr
                        push!(next_layer_buf, nxt)
                    end
                end
                
                found && break
            end

            # forward_layerとnext_layer_bufの参照が同じになるといろいろとまずい
            # のでforward_layerに渡すのではなく入れ替えるという天才
            forward_layer, next_layer_buf = next_layer_buf, forward_layer

        else # backward_layerのほうが短い
            for curr in backward_layer
                
                empty!(local_transitions)
                get_next_states!(local_transitions, curr, allow_same_char)

                for nxt in local_transitions
                    
                    if nxt[1] > max_length
                        continue
                    end

                    if nxt ∈ forward_visited
                        push!(backward_visited, nxt)
                        collision_node = nxt
                        found = true
                        break
                    end

                    if nxt ∉ backward_visited
                        push!(backward_visited, nxt)
                        push!(next_layer_buf, nxt)
                    end
                end

                found && break
            end

            backward_layer, next_layer_buf = next_layer_buf, backward_layer
        end

        found && break
    end

    if found
        return step
    else
        return -1
    end
end

function bidirectional_bfs_prove(start_str::String, target_str::String; allow_same_char::Bool=true, max_depth::Int=30, max_length::Int=15)
    if start_str == target_str
        println("start_str and target_str are the same")
        return true
    elseif length(start_str) <= 1 || length(target_str) <= 1
        println("Theoretically, there is no solution.")
        return false
    end

    start_set = Set(start_str)
    target_set = Set(target_str)
    if start_set != target_set
        println("Theoretically, there is no solution.")
        return false
    end

    all_chars = unique(start_str)
    char_to_id = Dict(c => i for (i, c) in enumerate(all_chars))
    id_to_char = Dict(i => c for (i, c) in enumerate(all_chars))

    start_word  = encode_word([char_to_id[c] for c in start_str])
    target_word = encode_word([char_to_id[c] for c in target_str])

    forward_visited  = Dict{Word, Word}(start_word => start_word)
    backward_visited = Dict{Word, Word}(target_word => target_word)

    # 探索の最前線にいるノードの集合
    forward_layer  = Set{Word}([start_word])
    backward_layer = Set{Word}([target_word])
    # 一時置き場
    # next_layer_buf: 「階層全体（世代全体）」 の次の最前線ノードをすべて集める大きな器。
    # local_transitions: 「今処理しているノード1個だけ」 から派生する遷移先を、アロケーションフリーで一時的に計算するための小さな作業机。
    next_layer_buf = Set{Word}()
    local_transitions = Set{Word}()

    function word_to_str(w::Word)::String
        return join([ id_to_char[w[i+1]] for i in 1:w[1] ])
    end

    println("Initial state: ", start_str, " <---> Target state: ", target_str)
    println("Maximum depth: ", max_depth, " (Maximum character length limit: ", max_length, ")")

    found = false
    collision_node = start_word

    for step in 1:max_depth
        if isempty(forward_layer) || isempty(backward_layer)
            break
        end

        empty!(next_layer_buf)

        if length(forward_layer) <= length(backward_layer)
            # forwardが短いので、そちらを展開する
            @showprogress "Forward  Layer $step" for curr in forward_layer
                
                empty!(local_transitions)
                get_next_states!(local_transitions, curr, allow_same_char)
                # local_transitionsにcurrから行けるやつが全て入った

                for nxt in local_transitions
                    
                    if nxt[1] > max_length
                        continue
                    end

                    if haskey(backward_visited, nxt)
                        forward_visited[nxt] = curr
                        collision_node = nxt
                        found = true
                        break
                    end

                    if !haskey(forward_visited, nxt)
                        forward_visited[nxt] = curr     # 根へ向いた矢印をつける nxt→curr
                        push!(next_layer_buf, nxt)
                    end
                end
                
                found && break
            end

            # forward_layerとnext_layer_bufの参照が同じになるといろいろとまずい
            # のでforward_layerに渡すのではなく入れ替えるという天才
            forward_layer, next_layer_buf = next_layer_buf, forward_layer

        else # backward_layerのほうが短い
            @showprogress "Backward Layer $step" for curr in backward_layer
                
                empty!(local_transitions)
                get_next_states!(local_transitions, curr, allow_same_char)

                for nxt in local_transitions
                    
                    if nxt[1] > max_length
                        continue
                    end

                    if haskey(forward_visited, nxt)
                        backward_visited[nxt] = curr
                        collision_node = nxt
                        found = true
                        break
                    end

                    if !haskey(backward_visited, nxt)
                        backward_visited[nxt] = curr
                        push!(next_layer_buf, nxt)
                    end
                end

                found && break
            end

            backward_layer, next_layer_buf = next_layer_buf, backward_layer
        end

        found && break
    end

    if !found
        total_explored = length(forward_visited) + length(backward_visited)
        println("No solution was found.")
        println("Total number of states explored :", total_explored)
        #println(keys(forward_visited).|>word_to_str)
        #println(keys(backward_visited).|>word_to_str)
        return found
    end

    # Forward 経路の復元
    f_path = Word[]
    curr = collision_node
    # collision_nodeから根に戻る
    push!(f_path, curr)
    while curr != start_word
        curr = forward_visited[curr]
        push!(f_path, curr)
    end
    reverse!(f_path) # 根からcollision_nodeの順に直す

    # Backward 経路の復元
    b_path = Word[]
    curr = collision_node
    # collision_nodeの次から根に戻る
    while curr != target_word
        curr = backward_visited[curr]
        push!(b_path, curr)
    end

    println("A route has been found.")
    println("Number of moves : ", length(f_path)+length(b_path)-1)
    println()
    
    for w in f_path
        println(word_to_str(w))
    end
    for w in b_path
        println(word_to_str(w))
    end
    
    println()
    
    return found
end

# 例
# bidirectional_bfs_prove("ハロウイーン","ウーロンハイ", allow_same_char=true, max_depth=30, max_length=15)