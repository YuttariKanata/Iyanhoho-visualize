using DataStructures
using ProgressMeter

const MAX_LEN = 31

struct Word
    len::Int
    w::NTuple{MAX_LEN, UInt8}
end

function encode_word(vec::Vector{Int})::Word
    L = lastindex(vec)
    @assert L <= MAX_LEN "The string exceeds MAX_LEN($MAX_LEN)."
    return Word(L, ntuple(i -> (i <= L ? vec[i] : 0x00), MAX_LEN))
end

function get_next_states!(next_states::Set{Word}, w::Word, allow_same_char::Bool)
    L = w.len
    if L < 2
        return
    end

    if L+1 <= MAX_LEN
        for i in 1:(L-1)
            
            x = w.w[i]
            y = w.w[i+1]
            if !allow_same_char && x == y
                continue
            end

            # nxtの長さはw.len+1になる
            # nxtの1~i-1まではw.wと同じ
            # nxt[i]はyに、nxt[i+1]=nxt[i+2]=xになる
            # nxtのi+3~L+1までは、w.wのi+2~Lまでになる
            # nxtのL+2~は0
            nxt = ntuple(MAX_LEN) do j
                if j <= i-1
                    return w.w[j]
                elseif j >= L+2
                    return 0x00
                elseif j >= i+3
                    return w.w[j-1]
                elseif j == i
                    return y
                else
                    return x
                end
            end
            push!(next_states, Word(L+1,nxt))
        end
    end

    for i in 1:L-2
        y = w.w[i]
        x = w.w[i+1]

        if x == w.w[i+2]
            if !allow_same_char && y == x
                continue
            end

            # nxtの長さはw.len-1になる
            # nxtの1~i-1まではw.wと同じ
            # nxt[i]=xに、nxt[i+1]=yになる
            # nxtのi+2~L-1まではw.wのi+3~Lまでになる
            # nxtのL~は0
            nxt = ntuple(MAX_LEN) do j
                if j <= i-1
                    return w.w[j]
                elseif j >= L
                    return 0x00
                elseif j >= i+2
                    return w.w[j+1]
                elseif j == i
                    return x
                else
                    return y
                end
            end
            push!(next_states, Word(L-1, nxt))
        end
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
        return join([ id_to_char[w.w[i]] for i in 1:w.len ])
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
            @showprogress "Forward Layer $step" for curr in forward_layer
                
                empty!(local_transitions)
                get_next_states!(local_transitions, curr, allow_same_char)
                # local_transitionsにcurrから行けるやつが全て入った

                for nxt in local_transitions
                    
                    if nxt.len > max_length
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
                    
                    if nxt.len > max_length
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
    println("Number of moves :", length(f_path)+length(b_path)-1)
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