function steps(x)
    if x < -2
        y = 0.0
    elseif x < 0
        y = x + 2
    elseif x <= 1.5
        y = 2 - x * x
    else
        y = sin(x)
    end
    return y * x
end

function last_if(x, k::Int)
    if k >= 2
        x^2
    else
        cos(x)
    end
end
