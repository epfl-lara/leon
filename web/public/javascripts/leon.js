var editor = null;

function appendError(title, msg) {
    alert(title+": "+msg)
}

function loadExample() {
    var value = $("#example-loader").val()

    if (value) { 
        $.ajax({
          url: '/ajax/getExample/'+value,
          dataType: "json",
          success: function(data, textStatus, jqXHR) {
            if (data.status == "success") {
                editor.setValue(data.code);
                editor.selection.clearSelection();
                editor.gotoLine(0);
            } else {
                appendError("Loading example failed :(", data.errormsg)
            }
          },
          error: function(jqXHR, textStatus, errorThrown) {
            appendError("Loading example failed :(", errorThrown)
          }
        });
    }
}

$(document).ready(function() {
    editor = ace.edit("codebox");
    editor.getSession().setMode("ace/mode/scala");
    editor.getSession().setUseWrapMode(true);

});

